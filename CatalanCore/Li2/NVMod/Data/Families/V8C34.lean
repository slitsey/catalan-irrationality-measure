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
namespace CatalanCore.Li2.NVMod.FamilySource.V8C34
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,8,34,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6,7]
def indices : List ℕ := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
def num : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def den : List ℤ := raw_ints% [0x54f1cf12bd04e516b6da88000000,0x7f1272ea095b3d484b2bfec00000,0x5aa8c58a87e6f43b15d03d540000,0x2911e5db14491c885d5997860000,0xd44e2039ac2445a6081ab43b000,0x3416cd88b0c83fe04095e008400,0xa17066246f775301dda13cb100,0x195718ceb07d78d8cc466004c0,0x3484cb018344757a2e6b8a080,0x5b02806082980dd615b89c30,0x851e3b4ac3644b56e0d7220,0xa573be53083492dc773824,0xaf87688d7b6d77699a438,0x9f5ed622ccb8b7a8b815,0x7bf3c2e61bd25299d19,0x52861d42be50a62696,0x2eeafe15d6c806e1a,0x16ae7c9e1ef41d8b,0x9436bc7917f3df,0x32ab12e24bde8,0xe503cb26ee4,0x3481719abb,0x98556787,0x1504bfe,0x212aa,0x215,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x1,0xb,-0x8f,0x1b5f,-0x8f,0x8f,-0xa16f,0xa16f,-0x14b1f5,0x14b1f5,-0x4e0139,0x19789,-0x242f7713,0x242f7713,-0x321567b,0x28b1643f,-0x1cdb67,0xa9aded,-0x3cac037,0x89e407d,-0x2ef7dd47,0xfa7f46d,-0xa05175]
def rhoDenominators : List ℤ := raw_ints% [0x21e5b41666c700,0x449087b2f00,0x3a8228b40,0x9150840,0x204ac80,0xec9280,0x27ebec0,0x10bc0,0x1dc0,0x4fbc0,0xf618,0x7c128,0x26490,0x374d0,0x888,0x7078f8,0x4ffb00,0x60b00,0x54b7c0,0x50c0,0x32780,0x27be80,0x10b2b40,0x1800e2c0,0x3601fe30,0x1eff0730]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-8) 0:ℚ)/(rhoDenominators.getD (m-8) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 8
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 8 34
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤33))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤33 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 34 omega8=padCoefficients 34 (omegaCoefficients 33 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 33 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 34 omega9=padCoefficients 34 (omegaCoefficients 33 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 33 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 34 omega10=padCoefficients 34 (omegaCoefficients 33 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 33 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 34 omega11=padCoefficients 34 (omegaCoefficients 33 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 33 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 34 omega12=padCoefficients 34 (omegaCoefficients 33 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 33 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 34 omega13=padCoefficients 34 (omegaCoefficients 33 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 33 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 34 omega14=padCoefficients 34 (omegaCoefficients 33 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 33 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 34 omega15=padCoefficients 34 (omegaCoefficients 33 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 33 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 34 omega16=padCoefficients 34 (omegaCoefficients 33 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 33 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 34 omega17=padCoefficients 34 (omegaCoefficients 33 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 33 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 34 omega18=padCoefficients 34 (omegaCoefficients 33 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 33 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 34 omega19=padCoefficients 34 (omegaCoefficients 33 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 33 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 34 omega20=padCoefficients 34 (omegaCoefficients 33 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 33 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 34 omega21=padCoefficients 34 (omegaCoefficients 33 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 33 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 34 omega22=padCoefficients 34 (omegaCoefficients 33 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 33 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 34 omega23=padCoefficients 34 (omegaCoefficients 33 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 33 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 34 omega24=padCoefficients 34 (omegaCoefficients 33 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 33 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 34 omega25=padCoefficients 34 (omegaCoefficients 33 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 33 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums26 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens26 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4]
def omega26 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums26 omegaDens26
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_26 : padCoefficients 34 omega26=padCoefficients 34 (omegaCoefficients 33 26) := by decide +kernel
theorem omega_spec_26 : coefficientsPoly omega26=omegaNumerator 33 26 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_26
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums27 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens27 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9]
def omega27 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums27 omegaDens27
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_27 : padCoefficients 34 omega27=padCoefficients 34 (omegaCoefficients 33 27) := by decide +kernel
theorem omega_spec_27 : coefficientsPoly omega27=omegaNumerator 33 27 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_27
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums28 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens28 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310]
def omega28 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums28 omegaDens28
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_28 : padCoefficients 34 omega28=padCoefficients 34 (omegaCoefficients 33 28) := by decide +kernel
theorem omega_spec_28 : coefficientsPoly omega28=omegaNumerator 33 28 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_28
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums29 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens29 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349]
def omega29 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums29 omegaDens29
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_29 : padCoefficients 34 omega29=padCoefficients 34 (omegaCoefficients 33 29) := by decide +kernel
theorem omega_spec_29 : coefficientsPoly omega29=omegaNumerator 33 29 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_29
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums30 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens30 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384]
def omega30 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums30 omegaDens30
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_30 : padCoefficients 34 omega30=padCoefficients 34 (omegaCoefficients 33 30) := by decide +kernel
theorem omega_spec_30 : coefficientsPoly omega30=omegaNumerator 33 30 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_30
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums31 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens31 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384,0x3c1]
def omega31 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums31 omegaDens31
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_31 : padCoefficients 34 omega31=padCoefficients 34 (omegaCoefficients 33 31) := by decide +kernel
theorem omega_spec_31 : coefficientsPoly omega31=omegaNumerator 33 31 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_31
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums32 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens32 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384,0x3c1,0x400]
def omega32 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums32 omegaDens32
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_32 : padCoefficients 34 omega32=padCoefficients 34 (omegaCoefficients 33 32) := by decide +kernel
theorem omega_spec_32 : coefficientsPoly omega32=omegaNumerator 33 32 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_32
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums33 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens33 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384,0x3c1,0x400,0x441]
def omega33 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums33 omegaDens33
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_33 : padCoefficients 34 omega33=padCoefficients 34 (omegaCoefficients 33 33) := by decide +kernel
theorem omega_spec_33 : coefficientsPoly omega33=omegaNumerator 33 33 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_33
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x17,0xfd,-0x6eb,0x2297,-0x8371,0x18a53,-0x3bda5,0x77b4a,-0xc7826,0x117502,-0x14a18e,0x14a18e,-0x117502,0xc7826,-0x77b4a,0x3bda5,-0x18a53,0x8371,-0x2297,0x6eb,-0xfd,0x17,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 25 li0=padCoefficients 25 (liCoefficients 24 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 24 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x16,0xe7,-0x604,0x1c93,-0x66de,0x12375,-0x29a30,0x4e11a,-0x7970c,0x9ddf6,-0xac398,0x9ddf6,-0x7970c,0x4e11a,-0x29a30,0x12375,-0x66de,0x1c93,-0x604,0xe7,-0x16,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 25 li1=padCoefficients 25 (liCoefficients 24 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 24 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x14,0xbd,-0x460,0x122f,-0x381c,0x847b,-0xf240,0x154aa,-0x16148,0xe5a2,0x0,-0xe5a2,0x16148,-0x154aa,0xf240,-0x847b,0x381c,-0x122f,0x460,-0xbd,0x14,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 25 li2=padCoefficients 25 (liCoefficients 24 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 24 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x10,0x6f,-0x190,0x1db,0xab0,-0x47eb,0xf240,-0x237c6,0x3f160,-0x5829a,0x626a0,-0x5829a,0x3f160,-0x237c6,0xf240,-0x47eb,0xab0,0x1db,-0x190,0x6f,-0x10,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 25 li3=padCoefficients 25 (liCoefficients 24 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 24 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x8,-0x1b,0x2c0,-0x1339,0x5028,-0xe6e5,0x1e480,-0x2ed76,0x33bb0,-0x22dae,0x0,0x22dae,-0x33bb0,0x2ed76,-0x1e480,0xe6e5,-0x5028,0x1339,-0x2c0,0x1b,0x8,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 25 li4=padCoefficients 25 (liCoefficients 24 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 24 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x8,-0xf9,0x7d0,-0x214d,0x5268,-0x5b0b,-0x8c40,0x3629a,-0x83270,0xd1ab6,-0xf3720,0xd1ab6,-0x83270,0x3629a,-0x8c40,-0x5b0b,0x5268,-0x214d,0x7d0,-0xf9,0x8,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 25 li5=padCoefficients 25 (liCoefficients 24 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 24 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x28,-0x213,0x8c0,-0x181,-0x8bc8,0x2c23b,-0x7ab80,0xe07ea,-0x112970,0xc3a42,0x0,-0xc3a42,0x112970,-0xe07ea,0x7ab80,-0x2c23b,0x8bc8,0x181,-0x8c0,0x213,-0x28,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 25 li6=padCoefficients 25 (liCoefficients 24 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 24 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x68,-0x261,-0xaf0,0x9c8b,-0x2c6b8,0x6b4d5,-0x7c140,-0x43206,0x22a650,-0x471cfa,0x57d860,-0x471cfa,0x22a650,-0x43206,-0x7c140,0x6b4d5,-0x2c6b8,0x9c8b,-0xaf0,-0x261,0x68,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 25 li7=padCoefficients 25 (liCoefficients 24 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 24 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xe8,0x2b5,-0x5b00,0x1d8f7,-0x33108,-0x63825,0x2dc000,-0x741636,0xa77a90,-0x81abce,0x0,0x81abce,-0xa77a90,0x741636,-0x2dc000,0x63825,0x33108,-0x1d8f7,0x5b00,-0x2b5,-0xe8,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 25 li8=padCoefficients 25 (liCoefficients 24 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 24 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1e8,0x1df7,-0x11530,0x10ba3,0x10ffc8,-0x53fbcb,0xb049c0,-0x887e26,-0xcb01b0,0x2cb5056,-0x3ca6920,0x2cb5056,-0xcb01b0,-0x887e26,0xb049c0,-0x53fbcb,0x10ffc8,0x10ba3,-0x11530,0x1df7,0x1e8,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 25 li9=padCoefficients 25 (liCoefficients 24 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 24 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3e8,0x87bd,-0x157c0,-0x11c551,0x681678,-0xb1d005,-0xc33a80,0x574f22a,-0xa7882f0,0x929d922,0x0,-0x929d922,0xa7882f0,-0x574f22a,0xc33a80,0xb1d005,-0x681678,0x11c551,0x157c0,-0x87bd,-0x3e8,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 25 li10=padCoefficients 25 (liCoefficients 24 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 24 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7e8,0x1f50f,0x7b890,-0x6bfd05,0xb2e4c8,0x327c915,-0xec0db40,0x1628003a,-0xb2ecb0,-0x2e7dc15a,0x48a24560,-0x2e7dc15a,-0xb2ecb0,0x1628003a,-0xec0db40,0x327c915,0xb2e4c8,-0x6bfd05,0x7b890,0x1f50f,0x7e8,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 25 li11=padCoefficients 25 (liCoefficients 24 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 24 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfe8,0x69d05,0x4e9980,-0x132ec59,-0x5055708,0x1da53e9b,-0x22bd4100,-0x4762f2f6,0xfdf7d190,-0x10b386eee,0x0,0x10b386eee,-0xfdf7d190,0x4762f2f6,0x22bd4100,-0x1da53e9b,0x5055708,0x132ec59,-0x4e9980,-0x69d05,-0xfe8,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 25 li12=padCoefficients 25 (liCoefficients 24 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 24 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fe8,0x1554e7,0x1da9c50,0x1fffc93,-0x32e79838,0x423cff75,0x1244c1fc0,-0x38a027ae6,0x232df7850,0x49b0029f6,-0x8f6dd7820,0x49b0029f6,0x232df7850,-0x38a027ae6,0x1244c1fc0,0x423cff75,-0x32e79838,0x1fffc93,0x1da9c50,0x1554e7,0x1fe8,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 25 li13=padCoefficients 25 (liCoefficients 24 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 24 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fe8,0x42fc8d,0x96d64c0,0x388189df,-0xd2ec4888,-0x2978a0045,0xaf0e3f480,-0x2a4706196,-0x21bddae1f0,0x2fb35f8002,0x0,-0x2fb35f8002,0x21bddae1f0,0x2a4706196,-0xaf0e3f480,0x2978a0045,0xd2ec4888,-0x388189df,-0x96d64c0,-0x42fc8d,-0x3fe8,-0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 25 li14=padCoefficients 25 (liCoefficients 24 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 24 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fe8,0xcef37f,0x2c033e10,0x20316ce6b,0x1432a56c8,-0x1fb638c4ab,0xbc0bcdac0,0xa30708b47a,-0xd60619d6b0,-0xa1b2f7b1ba,0x1ca68e1ce60,-0xa1b2f7b1ba,-0xd60619d6b0,0xa30708b47a,0xbc0bcdac0,-0x1fb638c4ab,0x1432a56c8,0x20316ce6b,0x2c033e10,0xcef37f,0x7fe8,0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 25 li15=padCoefficients 25 (liCoefficients 24 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 24 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffe8,0x278d855,0xc37fca00,0xe4332ab57,0x3c10e205f8,-0x8b31b140a5,-0x248458f7a00,0x42f058c8a4a,0x560320cba90,-0xd46d401a60e,0x0,0xd46d401a60e,-0x560320cba90,-0x42f058c8a4a,0x248458f7a00,0x8b31b140a5,-0x3c10e205f8,-0xe4332ab57,-0xc37fca00,-0x278d855,-0xffe8,-0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 25 li16=padCoefficients 25 (liCoefficients 24 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 24 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffe8,0x78286d7,0x3496b6dd0,0x59df648e83,0x2d1417369c8,0x33c157f10b5,-0x184463c20a40,-0x17218ac8cda6,0x5d61bcf29650,0x16995d92a796,-0x95ff6682c720,0x16995d92a796,0x5d61bcf29650,-0x17218ac8cda6,-0x184463c20a40,0x33c157f10b5,0x2d1417369c8,0x59df648e83,0x3496b6dd0,0x78286d7,0x1ffe8,0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 25 li17=padCoefficients 25 (liCoefficients 24 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 24 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffe8,0x16b7925d,0xdda1a5940,0x210f375b60f,0x19a410a0c478,0x62ff4137a97b,-0x28266f688c80,-0x27c9a8c986b56,-0x31c04ce298f0,0x5e22f0daed2e2,0x0,-0x5e22f0daed2e2,0x31c04ce298f0,0x27c9a8c986b56,0x28266f688c80,-0x62ff4137a97b,-0x19a410a0c478,-0x210f375b60f,-0xdda1a5940,-0x16b7925d,-0x3ffe8,-0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 25 li18=padCoefficients 25 (liCoefficients 24 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 24 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw19 : List ℤ := raw_ints% [0x0,0x1,0x7ffe8,0x4486b4ef,0x3989ff1b90,0xba3555aa2db,0xccbdcadbc0c8,0x54f41beaf3395,0xaa101981d10c0,-0xe42d44fc77d46,-0x3581658d8fc0b0,0x87e1bd48ef1e6,0x54fa7f866fa760,0x87e1bd48ef1e6,-0x3581658d8fc0b0,-0xe42d44fc77d46,0xaa101981d10c0,0x54f41beaf3395,0xccbdcadbc0c8,0xba3555aa2db,0x3989ff1b90,0x4486b4ef,0x7ffe8,0x1]
def li19 : List ℚ := liRaw19.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_19 : padCoefficients 25 li19=padCoefficients 25 (liCoefficients 24 19) := by decide +kernel
theorem li_spec_19 : coefficientsPoly li19=liNumerator 24 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_19
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw20 : List ℤ := raw_ints% [0x0,0x1,0xfffe8,0xce541ca5,0xec955d6280,0x3f9c0810b807,0x5e92e1ef152f8,0x397952992f4a1b,0xe8c4bd03ba3d00,0x1127b5fb787e18a,-0x1da7d087cc5fc70,-0x46a2564187e212e,0x0,0x46a2564187e212e,0x1da7d087cc5fc70,-0x1127b5fb787e18a,-0xe8c4bd03ba3d00,-0x397952992f4a1b,-0x5e92e1ef152f8,-0x3f9c0810b807,-0xec955d6280,-0xce541ca5,-0xfffe8,-0x1]
def li20 : List ℚ := liRaw20.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_20 : padCoefficients 25 li20=padCoefficients 25 (liCoefficients 24 20) := by decide +kernel
theorem li_spec_20 : coefficientsPoly li20=liNumerator 24 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_20
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw21 : List ℤ := raw_ints% [0x0,0x1,0x1fffe8,0x26c7c53c7,0x3c5aed83750,0x1544d82778173,0x2983f6d55d1bc8,0x2263a77329ff7f5,0xd3d6edb7c95cbc0,0x257011092c00899a,0x22fc69500d3ae450,-0x27860873d30456ca,-0x60e9ee89116c0620,-0x27860873d30456ca,0x22fc69500d3ae450,0x257011092c00899a,0xd3d6edb7c95cbc0,0x2263a77329ff7f5,0x2983f6d55d1bc8,0x1544d82778173,0x3c5aed83750,0x26c7c53c7,0x1fffe8,0x1]
def li21 : List ℚ := liRaw21.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_21 : padCoefficients 25 li21=padCoefficients 25 (liCoefficients 24 21) := by decide +kernel
theorem li_spec_21 : coefficientsPoly li21=liNumerator 24 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_21
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw22 : List ℤ := raw_ints% [0x0,0x1,0x3fffe8,0x74874f92d,0xf50ea08b5c0,0x700461f428f3f,0x11959cfce4fd178,0x13103a6d313b8d3b,0xa185933372896280,0x2c64d1a3dc7eaf4ea,0x655ba36e7e03ff010,0x68cc59c4e8848b1c2,0x0,-0x68cc59c4e8848b1c2,-0x655ba36e7e03ff010,-0x2c64d1a3dc7eaf4ea,-0xa185933372896280,-0x13103a6d313b8d3b,-0x11959cfce4fd178,-0x700461f428f3f,-0xf50ea08b5c0,-0x74874f92d,-0x3fffe8,-0x1]
def li22 : List ℚ := liRaw22.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_22 : padCoefficients 25 li22=padCoefficients 25 (liCoefficients 24 22) := by decide +kernel
theorem li_spec_22 : coefficientsPoly li22=liNumerator 24 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_22
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw23 : List ℤ := raw_ints% [0x0,0x1,0x7fffe8,0x15df5ee95f,0x3df2791a3110,0x2471a35e15304b,0x74191b685e4bac8,0xa07b7b4f602251d5,0x6f0bbf62b3961c6c0,0x2a01cb158e693a8afa,0x92f995c43be27e4550,0x133b6427c4a011d0986,0x188dc4b6c46ecce1060,0x133b6427c4a011d0986,0x92f995c43be27e4550,0x2a01cb158e693a8afa,0x6f0bbf62b3961c6c0,0xa07b7b4f602251d5,0x74191b685e4bac8,0x2471a35e15304b,0x3df2791a3110,0x15df5ee95f,0x7fffe8,0x1]
def li23 : List ℚ := liRaw23.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_23 : padCoefficients 25 li23=padCoefficients 25 (liCoefficients 24 23) := by decide +kernel
theorem li_spec_23 : coefficientsPoly li23=liNumerator 24 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_23
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x18,0x114,-0x7e8,0x2982,-0xa608,0x20dc4,-0x547f8,0xb38ef,-0x13f370,0x1ded28,-0x261690,0x29431c,-0x261690,0x1ded28,-0x13f370,0xb38ef,-0x547f8,0x20dc4,-0xa608,0x2982,-0x7e8,0x114,-0x18,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 24 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^24 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
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
  | 31=>omega31
  | 32=>omega32
  | 33=>omega33
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
  | 22=>li22
  | 23=>li23
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 33 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 8 34 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
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
  · exact omega_spec_31
  · exact omega_spec_32
  · exact omega_spec_33
theorem cache_li (j : ℕ) (hj : j<24) : coefficientsPoly (cache.li j)=liNumerator 24 j := by
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
  · exact li_spec_22
  · exact li_spec_23
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x1a9baa4a3a83fadacc8620befe9000,0x3f5b6fee90d993e16dbfa014b5cec00,-0x498f37d94cc225870e17ab3de60d5800,0x377d7bf8a3245bf164d30068296d0a800,-0x1e93e3601cde06956d129cfce95960b600,0xd1ec9dd76ac57042b2713066a3ba8e80c0,-0x490235358d05e32204c21f1a87a7ca5b5c0,0x15272e5043f0e7082e10cce2c4a8209de720,-0x53543dc3f28d798ea400af0bb4635a419b20,0x11b250702c632ec0a5b1398bac966fbdaac50,-0x347838ba987d4b3dfba3af93d09929ff02490,0x88fe909fb2414772f3efa7c9e007f48db7a28,-0x13d4a4f9c06ad6dbc1f9ef0d7402653d6bf568,0x28fc4a97f2ab58a60e128bf8160b832f7ed390,-0x4bf4f953ca3cbe47360ece52b66a84fdf51650,0x7eb9d375c78e20ec2a554f8f2033917140f684,-0xbef3643ac64cb212a2959275a674062bb2c3c4,0x104883cc5e6c0d6c39cf5bfe8465b1b0c2b0374,-0x14288dc8805c9451e0a4efe1293020442ed7544,0x16ade693021a0a84b7c4475b54ab29bcf5fdae6,-0x1736e1c184e92b96b683c3521ebbe2fc945bcf6,0x15a29f0cd169448a86c18b1ca09da701bfeed64,-0x125d9243504c73d980ab4d0ca53c49f641577d4,0xe332907e01513494cb1c9bc422d53fac34dd09,-0x9ff1ea51d480121336de9f44a7d193648aa3d9,0x667366a5c56dbcf27d136cb178cb4ace720058,-0x3ba4e8490ea29b6a9b81b381d8210658864c38,0x1f835688ef46b32b31315101ccbad119ca9c5c,-0xf1506d613e8f3cf533ee48556de917c0382bc,0x685f871d48f54ef1e00c3cad6c67b60cfd508,-0x28ae57e49377d521ea2394541af687937b868,0xe3d6b961276c0aa9d438ab86f2d0f68d0e0b,-0x47550fa0110c7373c90347819cbd3febbc0b,0x13e0e5ef6027b7b7ba5e87fb6c82ee9b6284,-0x4e70d0396ce631c28f87b93ad25f4942a14,0x1100eb5fc1a02d94b3673f0a06c96e8a196,-0x336933982741bd510211a36f768b6c6766,0x862c25d367c098b4c9795203e1eac58b4,-0x12a9ee082bf90df83a83d6d9b217fa964,0x22e67a53d93dfcb01700ac4a2dbbbd4f,-0x35d09bc44f056013cd1135bc042e89f,0x42cdb8e677be3e27a084ff8f363de0,-0x40afa6f0d93ef7f60723fa3f0cb60,0x2ecd99c262ff775fd1ac581e3160,-0x17cda23fcd04f13afe0d829c8e0,0x7c211a7040cdb1f942136fc10,-0x1643196fb352ea1f10f70ed0,0x1a5c3e13c5173b06606599,-0x662972bd6ec3952c539]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 26 45 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 45 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 58 indices rho q0 m0 0 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 58 indices rho q0 m0 0 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x36e10f3918b0356345d4a389ed09000,-0x812ed0e984a0e648a7f8b1b323bb5c00,0x943e92578e0e44317fe36b7947acb4400,-0x6e82660a5d13ba5241816d56711cf21a00,0x3c2a16c22c99fb757b82323cdae9f423400,-0x197feba35d8d18c4f0dcd7407f3b9ed5ba40,0x8c20c22fc93efa64471106a64734c1f54180,-0x2815b24497d57d255ccddf4d2a5395a2743a0,0x9bdda68bb67d9164f8796048243094f508280,-0x20aa2a5cff42e87e74f48918ca5557d2bbc330,0x5f8c098b5b0699b70353125f9b1c19e8d693e0,-0xf60a99b2abaa0158106712e2e3cd36f0710448,0x231dcb2fdeda4cde81a6bd6368e4df06185cee0,-0x4789b234c546448726c63d23692ba8dbafee6b0,0x82a2e7cd677b62d01cd17b7271ff16aecccd620,-0xd6afa23d4a38bacaf264529ba08cb7199b1efe4,0x13e86a1b56ac7b4a52ac7d1a2400a9893c1fbac0,-0x1abc380f3a96a750d9f3ccca1ea1f9947ab5ce0c,0x20907bbd334eca2e49edbb3d39ea4feb5c08e7d8,-0x2407e7a0c9c17c4471fcbf4baddd3fd6e361a78e,0x24413432fe20fd961646d4b2eac0ceb1f4c4ccf8,-0x2132e284cd7372bb8f2a6de5e59a52f481c46f8c,0x1bace6edbaef67ed2bb3c7edcfc3e03879941ce8,-0x150098bca84aed0d2bd73ce20954b5d5323b8081,0xe80e6f40bccb4140341b676838364b5fa7b96d0,-0x91b7142606e498f2c985a843fdcb68c81ecdf68,0x531b0f9f436b3904bcc5f3c737732c9e9248890,-0x2afbfea289b3aba11aae319a77e402295038ccc,0x141f8d0a3ddec67dd1eeef1389081e09d421290,-0x881a58ba5589912039d24d41e1d4dbe63e7918,0x33cc28a0c250f72747faedaba7fdeec1eb9590,-0x11af8160e7c26fe6957c0b04e0f5875223f95b,0x565189a278fbc1801d943344cb14b322e9c58,-0x176881b89869005f6d18006cdda6c9211efbc,0x59c3187a67224c949745b1dc8e15c1dffb78,-0x12e11eef29090f6d2c7a19d19a7f14a5759e,0x374a10674baae347fb50e8790eb6d274ad8,-0x8b7c2cf27dc356c1bb040ea480888636bc,0x12b6ad326ecb0073906e8d18e7ae8a4bc8,-0x21a967a7ed936d899332f06faaf3935a7,0x31c6a72507d23d9931bf609417eace40,-0x3b09cc2dd318d26ffba71c3ec4ba9a0,0x366119342ab2423677e4c5e57a99c0,-0x2539083a717b95314bef5526786a0,0x11c945e59bf4489e036b3fb75840,-0x565e38c0b28a7a5efac1db81b0,0xe40cff9844fd9058d6250ca0,-0xf48017961bd950db882619,0x347c2bb42aaaffe1abd8]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 26 46 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 46 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 58 indices rho q1 m1 1 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 58 indices rho q1 m1 1 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x71302f65c2eb6e1cc006914c78e29000,0x1077502fc954c258545abdd9253344dc00,-0x12ae38e139e8bc844b556746fac7a649c00,0xdc39efd675f9e4385ea54992c6598f46c00,-0x767bba21f692e6839c51475889e34bfcfa00,0x319d3308d2b1f409c48476cabc8ceb83c36c0,-0x10d4ea7a1123c493f67e86f059836fb1f04d00,0x4c13ac661126826f2f59ae087c0188d265c620,-0x1240e679f5afc09780e512e09f4213220a54800,0x3c69811311b05ecf726b4591cd1566fd7a1a450,-0xae5efc6681d7821a67193a896920e4ed4ebdec0,0x1baf2fe7a34e1a0dc4a9785fa56b58df2939aa68,-0x3e58cc42bf82adcdeb7fd6cdb4f5688483644cc0,0x7d379ffe4c27fd4528580910ec837684a51d5dd0,-0xe15ba3f1c0da2a1a5ed06ee1436d91553bbf3b00,0x16cdfcb8cabfb56bf0dc10a7a688572bb49a50f84,-0x215287f07b9f2fefc2d6a6b3d34523dc0b1a44720,0x2c0e34f454262d617e0e0001c73ed084b44f33154,-0x34ce748bdeb6099f54fc3af5271d8d79aacaba990,0x3978f2c9c69958ec89a96b1bf1777aaf2a312fd16,-0x38dba28608c6c150518b8106339ded2fa081af270,0x332a6edb2546f43502065c57126cc410c5feb84b4,-0x29e4fb5cf64b79a925c1bfed8e8217a44b55e54c0,0x1f35c82e7d0cc4e672aa36e8a115a65447eedc849,-0x15252073a163a22d919e747a4687c52ccd82a7008,0xd04a756732c1a6575af63f25b2680c0081c383d0,-0x7464cbf984746df0b6609b5a6ac93baee0c40b28,0x3af106bd3fc6c588f36705d84aa19560a701d0b4,-0x1afe8e8b0c3293929c4766f41f4cf8fa7904f7a8,0xb2747645169f3b8328875ee16dbe423b8b7d660,-0x4251e0051ebf97c58812f288c4083a8a66b6b48,0x1616c549c6a77b11ee5293af7ee6f727b76f603,-0x690c08715c852471bf65b5c9e8fab24e121ab0,0x1bb8c7aac841f9d116947ee4e912c352508314,-0x674d25f87a420b50854f531078f667d829b20,0x1514882fe28c9eb21b2ee93ce013065c65336,-0x3bca3bbc493f9871e494fbd8f8215e9c7a40,0x91cade77ff726e1e9d6d385cd1cf9114c34,-0x12dc87d45ea5b6fa72838937415a776c950,0x20a0dd0d1229bbda5f78e6c28da9ccb07f,-0x2e40f6e2af40d4d0fbbae504a5e82fa68,0x34655883e55b400c8d3c6a31665b6378,-0x2de24e89e25ba09c83a44f0609bbce8,0x1db1c03ccfa5cfba8714d24a2a3978,-0xd5225f8eeed2d938b8c5426bd868,0x3c2e3fa9a374a0f83755fc45028,-0x9215eee2bef4e1fff07096728,0x8db5eae1234ccec17f4a2b1,-0x1af43ca6e204c7932d840]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 26 47 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 47 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 58 indices rho q2 m2 2 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 58 indices rho q2 m2 2 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m3 : List ℤ := raw_ints% [0x0,0xe97361c1e205931b4c0d8badb95349000,-0x2196a3e5edb6da281b628571f7e9fa05c00,0x25ae1574819a1357bd57ebef2dcac3aac400,-0x1b7293ed8c43a88012ba7c3c840ac07f83200,0xe989322c15006246a54716eac9f2363975e00,-0x60a3523bffaea34bfbe4f1882ab82dbbd29640,0x2063fad7658e8aab241287bc393aca76343be00,-0x909b214893262696c78d0424527b006b163cea0,0x224320f34baf41422f4a78f1982b2548606c2600,-0x6ff29c0d16a0d90dea671f5a853b9041cb56a530,0x13ee91f3fc88aa8284da8840daf27705a99573a00,-0x31f556666366e49c353ba5995e87ce73c0b185808,0x6efa724eaea64795d358b324e2a88442ecb8a3040,-0xdbc940e6b49031d6ca692c3e443c81264d20cde30,0x185ec0683f1caa4b2b8ad0ab59e97ac6ba7ff06cc0,-0x26e1b728d5b229cc53ff9260b8d5360552f513b424,0x37f703ab329ba1e7472721628155b0c4e497dd2120,-0x48db45d691cb5a30df27e8ad0ca05408e3706cbe0c,0x55f434e4835ae0fe9ffd8c321fb3d36df13bb4c4e0,-0x5c094dbac77e3ae541838eb75c0a14cf96ff132efe,0x5989e7e3ee0386736ef441258154ec193b94656ed0,-0x4f3242ab6bfeb52d02746146dde909215852437bec,0x3fb3fc3f7080ee7107e6f321758ba9b5dc12242070,-0x2e982608b80837bc9d83dffa49cd0cc0a43d452b51,0x1ef9c083b591c8b00aa101a430fe9b7a3d22834788,-0x12b357a0ec530aa0bd61c19b072c59e9a5aa918a28,0xa3d7820e31e2123c8bfd9fd2495f343e4c56fccf8,-0x513df8d22f05ba7513e2547284fc9be32e060703c,0x24674f7c0227224dc80f6d22901579c3e2c2ecdc8,-0xeb3f712e1b9f35b515182f89d3e2b7cf90aa20b8,0x5560ce8173a10c8cff35021013d704e1b562f2f8,-0x1bbdbad0ac738a2bbdc8824536f8d3f77a28a9ab,0x808cbc3f3e6835e4bd128d55ef3af480789a370,-0x210356c9f42d0d1c865a76c527f0ba24f01223c,0x778ace1116424aec6ddbef06c3adf105a57190,-0x17aab52bf73eed970a3fa8ba108c6283f46c6e,0x41018028d2063bf5a24511b0fc01e80b478e0,-0x992f8af294f5aa32fc5e119e82ae20b1365c,0x131b4d662f38dc4fa2357dcb565216eabde0,-0x1fc74e3055dcd3a67b5fb089e93a6557997,0x2b2c3c05c51c320d7b2b53b47b9e882068,-0x2eb06754e6d1c1a01e3fafe97adbafe60,0x26da408fd3ed62194dd1cbc63799fe18,-0x17c1daf975f194b70979e96dfeda930,0x9ff8353cbc1876bad5fec98c503c8,-0x29fd09676d316bb33ecc44fef690,0x5d9f468e90fcc0b4d728240478,-0x521dd3d23819434d49b047c9,0xdd6688ae0df5e190dd600]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 26 48 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 48 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 58 indices rho q3 m3 3 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 58 indices rho q3 m3 3 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x1e17df99fe22b7f684cdbf0164e3bc69000,0x4487cf10f73934969349eeff45b30babdc00,-0x4c0945beb002e6e7a61bbefdcd0cf6bb59c00,0x36c50c290acc45a5d87af9ee9f0a3187b1bc00,-0x1ccb5360467585e551d0b5667524e460be01600,0xbc6f1e96e4e04e9b1d1cf3e716b629fc46f42c0,-0x3e69889f976747d6e162baf34b6b3d5a02e6e800,0x113477f4b8a76e9a05938b3a97ede95ce28fb5920,-0x406bdd67407084cb8e01ef508201df28f84811600,0xcfd8b1b6d96074e9d1fe353284a5eaccb7e876250,-0x248821351e984e348f2a1d1425e2843b22e0a8e480,0x5a5d5c89dd21f1ce9df1e8ea650452d236adcdd628,-0xc60bde27bb84b3d6b84da24bd0f4e7f62bb3357040,0x182d6971b4699f1b23827e5f344ee2d6b511f961250,-0x2a4a5a298a35dcdd7bdbdb5e79578a87601824a7d40,0x42806b6056892713e6a5d5d2afef1742e980c323ec4,-0x5e4e9c51dff25c001d93eed4bf955613e4c25701120,0x78e9617c459fe31f0135d321bca64a56949aea04954,-0x8c6dc3a154c8cf09f026c5d171d4a25f3762c5c2780,0x93f62d6381ee0abd562227ccb10ec4e62e5cfc29786,-0x8d940b41e16c4b281777f93674f0ad14215a26cd4d0,0x7b1a856b63519e346c9b7e2d197d1d37aeea1c34154,-0x614aa012167a09a9a0228f4df352ab61ccd41df0610,0x45e12546a66b8dba3453883c3c9c0275300c7dc22d9,-0x2d972546ffe85107d1d268936f25570650f2fc5f788,0x1afe5e7839720168e32ed0f5ffb9f4c5b07e3a18710,-0xe7c7f063bb8f9dff73d72aee6402fbaea2b709af18,0x708d08212fa11e4ea0d951953993406fdfcbefc2a4,-0x31590552e138b7de6bd9f4b7cba79fb785c1efc5c8,0x137c1404245d6e8bd1da820da5e50a1d7bfa73f1c0,-0x6e80940d2ec4b022e653774ad26207e8b0ecf4218,0x23072feb7da2a93652f5fcb823ab70250d0669693,-0x9e2a91a7eed206fe3770971dd0b1f626ee49c570,0x278731491bf4053873de026de54e09f8637adc94,-0x8b15cdeaef66fe921e02346f5bdb2cbe552ad70,0x1ab68883d7ed39090ff96a0af7df2c93c8a5406,-0x470c3c68a71d73d9cf7068fdefb8ce6a64a6e0,0xa1c66d7c6bb33755a539e3286645c729a0394,-0x13732c8f83dce868e28b9e45356ba7beafcc0,0x1f1827dcce8369595775e2f9ec0b4977c4af,-0x28786731d01a93ef188ae34b6d05d073468,0x29c3e48f66c3de5878cccb7f6e1c408cb8,-0x2102590c6427dee2494144aeab97ba2f8,0x130f292517e53deed1642cd7f28f4888,-0x784e97537bbf4c129e80f74c34ffc8,0x1d54955bc1c396708d5cf21aea448,-0x3c05b02012dfd830bafbbc6ae58,0x2f9292cf19eea860a8596b921,-0x719f4c9ad20d7736819000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 26 49 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 49 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 58 indices rho q4 m4 4 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 58 indices rho q4 m4 4 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x3e113d2d9c279b6c71e859f2e015b4989000,-0x8bda552077c621be4565f476ec82381275c00,0x9980b9af8e2c2e0dae595211e0420a2801c400,-0x6d5c0513138ef4f9920d8e40f1c06476f779200,0x38da3af7d3423c7c135d39e04be5c2932ed4d600,-0x16fd1ceadaffa020c4042eccc090b55ebda39a240,0x7869f7e65958ee84e51e0df048975143584288800,-0x20cd10496c14f0d8dd3639ef4b149cb96eea740da0,0x79556ac11880067afce6466688dd4ce8f51b901e00,-0x182a1ab2ce3f1bbdb672b6d9e7023b3f8e069bc7f30,0x43190ab7901883b377448cc0c76917d5cfb3fd31280,-0xa3d48c1ea6cad1ff4d461b5d8a9e2959462787402c8,0x16250409d43af44c12e2899a3721744a497dd361fa40,-0x2aab602b11d9723fa6129e2c15d8013da94e00f5b3b0,0x499a2325ddb1f7d7ed7ca590937ae14b3963914adf40,-0x721855831103a2584c2b83c82fd953150e353fbc5f64,0x9f712224827028020ca1946ee9c888544196619f6120,-0xc95cbfcd230b3d579ae8298cafdea05f774a3e24be0c,0xe644e40fdb0eb4a2d8d09c768005a0b68fe5b260e100,-0xeec8a820887f24838524c86b61c4009ca0e0c536562e,0xe0c318dcf63605da32d79b8fd02ee748eb2b53fd6950,-0xc027593820d1786e69763bde2f6890628bb05439f1cc,0x953c2aceba6b43a72c3696fab18dd0a99445ed97c290,-0x6945a683aac21ade26d97df5cfa39a27c278445246e1,0x436970f4efc8ea6062768f974d64a718fc94b9518388,-0x272679a925e95c59134d1553d7af00be6f0a5fa8a8e8,0x1497f3192e60bd6a185d4964f5d95eab8b28860de398,-0x9cb4b88ebe359db03a904cd29c377fba98fc406c36c,0x433c66632f81c411cd105cece21429b73d2f7fa6e48,-0x19f493bdf67aae013d5fd53bd487738bbbcf84675d8,0x8fc5468248817242ee92b30855f24d83f25ffe1798,-0x2c769fc494613d7cc413b2ec6273e8fe01ec70d8bb,0xc3a427fcb78452ed6c7d64bd20d1a35c8b5a95170,-0x2f94985906c17d9f0fdec1b262e85a1ee27ee88bc,0xa2ad85d924f2dfe01b40dce38815aab0273ed3f0,-0x1e4efb0c1a3f7f860670db6c1ddcada1148e787e,0x4e0c418038ed9ac8cad01e20b503a951aa22c60,-0xabb1453f3bb6fbb91a70b077a3ba8b3313aa7c,0x13e4af58eb056cefc4dffd03100cf704729040,-0x1e8fa7a3d948b0b6b73213ebb8367c45415c7,0x26180e384bb94344b6f624e717a82e065468,-0x257fd463a4028a80e09765bd7aa51d36320,0x1c225e8410c7e75cbd53cd5d7ae55a8878,-0xf54638a549037ca509995d736e4a4800,0x5aa58880d34458846e8ce0852407348,-0x1482a461e31b577a354e95eb1a11f0,0x267e1e93f0bc6a8d2de927d736d8,-0x1b8da71f872b20146221e646b9,0x3a4a85b374a558cb7758000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 26 50 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 50 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 58 indices rho q5 m5 5 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 58 indices rho q5 m5 5 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m6 : List ℤ := raw_ints% [0x0,-0x80038e2e1211b08faaef3984ee2cc47aa9000,0x11d76c3adeac8f027da5d3746214e73a612dc00,-0x136066debf763aaf46fb5c3e632b840ed5b69c00,0xda7fa2d34d3cafd50a427ca561f7edf9f2017c00,-0x7058ca89737b1dc33b1e194a952335fe37d7f9600,0x2cebc590a5ec0985c021ff729ef827719673c25ec0,-0xe89cd6d2d6baaac7872029b74715735f23d6d64400,0x3ea07d93072d99b96033e01412ced91fa94299ddc20,-0xe4e8908307ae32e96f83e92c3ce1cec642b8555ee00,0x2d08f2411ec497eec39b19ae2f6a8309a072183c2850,-0x7b7ee87d68f70d9f4972211351550eaf70fc5e6e8380,0x129b3cc0adcea2ad986afb0df69ae6efd8973d6c9ade8,-0x27b756e470b26851cc453788b1761204c6cd88a2d4640,0x4b81d5fc06745c7656896e41b38426f4c258b470e20d0,-0x80771cb521e07425ee51f5ad9900f7c560e5836928040,0xc459a379278fcd2205ceb07f00dbd374c54bad2ffc204,-0x10e70bf35cc791d638cd3fb6cee5fc46ecacc70101f520,0x1507ea086c6346ff0fc92073c06f8079f89a9791e45d54,-0x17af351f6f87c3b9ae9db184d4ab72039123e3ef6c1340,0x182d09094d2203924e9e933acc1d8161d68bbc8fd8e8f6,-0x1663b6d29d15ce276ca172e2017f58d64396de5258d850,0x12d2b90be9c2c76654a16d71c377061880a21906447a74,-0xe5e3b0a19296225ef0d1e8b31d500481e2511a9e417d0,0x9f4aa7619b134df2a62f7071a76f9613bbd5b13df8e69,-0x6421f58e3f0583220b835e38a3fce1246c95429e03888,0x390c5004c6af0758c56450cd853eafb3b48c97cacf950,-0x1d6a94421711f9292eede9ed592d5311a88b24acd77d8,0xdb41912ca04f30a8ff15447318cda3df293e10fd4f94,-0x5c113da762e5a885bb7f12a9a0135c974b8c40dbb048,0x22c034bceeee8820d9ccee1d19f5cba92293052a3aa0,-0xbc047b3ad32b01ca3d0930d2684b56c8ea8132e08d8,0x38bb9f881ad54874c9c0ff25332070be3a479a26023,-0xf3411da00260b11104af26cbcb4808315fc6cb5f70,0x399214f487805e325979981db1df2cd306cda80c14,-0xbf40d456d2928f1e3e9ddefb2bfaae4919af568b0,0x22900caac546cf7cb25774d9c765a87861b70e9d6,-0x5629e0ec6fefae9dd9beb988f8f1188f8c15af60,0xb718128d033ca4b391b1f34222c7c9a04a61274,-0x1470b9a61b8ef6e6b75707a954b60d119330e00,0x1e2abb64717dc3791c2e575f279d67cd0cf3df,-0x23fff0c7e887ed882ec3bfde50058c97f3d68,0x21c9ec0c7f3bedfbea239f79e573d2601cf8,-0x180d54e4df6bd7e771f71b50ac4cd902438,0xc5c1a0fbb0449081efa007c74edf47498,-0x446a967698d5d3622c68c7a87407a348,0xe5b3e0cb909b5ea1dc03bc0b85dce8,-0x18b10c294d00827fb030a423dd598,0xff44eb971116bf172e7ff91691,-0x1de5202ed32ca7fa6d840000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 26 51 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 51 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 58 indices rho q6 m6 6 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 58 indices rho q6 m6 6 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m7 : List ℤ := raw_ints% [0x0,0x10807553f05447c28508d66a22b3c553cfc9000,-0x246cddbcc9bbf047108d6202257b58e8686e5c00,0x272697b70d48936b3e152d8512be6e9a78e98c400,-0x1b4d5025db9b94ae355fb55ea4c1592aabd6401200,0xde3236c97a4152117e8e68cd018b2b7b3689138600,-0x57de9269fbe6dc3c510a83024dbdb1746cef601ee40,0x1c1eb0b567822eba4efbab29a99148e11478ec4e4000,-0x77bf67c62064527be71ae13b0d8deb3b423b579d54a0,0x1b093a5535f037810fe1e14a7c62ae9571bf7460c6600,-0x541658c4794635abcee0ea9d4b539e316559d50207930,0xe3c452199592b7425baaf3bb7ca81d33e04620038bc80,-0x21e308c0adde0760c55da598e0cdcd916611e5ab7dbf88,0x4767d9ac5ecb348ecfda7854cc339308f27363b2b15c40,-0x85f86b280fa6dc319e6f81666347ecacc3dc48918bb930,0xe0dc454b6237e95cd252b2837f25560d1da0ec59171340,-0x152edbe2b99b344bb73e632f204471fa3100181d99102a4,0x1cc2f6f5890a90ceaf0285d332c09dd35b99f5dba187d20,-0x234381d81bccb7bd18567fd556da9b81b58f521cf68b60c,0x271db3afdc9ebac4b343a379d7767c2af93a12d4b79c580,-0x274f4a9c4ff20ff1ab57c55e08f32c403f3b1999a3197de,0x23d2fcefce5d34fae0eedcda8c38cb0d73c5480447effd0,-0x1d9f38b01a07b4d80ce2789fcb2a7b58585ea59484d0bac,0x1639fc64ce20203d1c3e7aa3537ef8968f65d70407ae390,-0xf2147686701e343cca3461cc7bd5c08111b939ac0efc71,0x95672e5266593a5e65a0d4b20fcff9562f2565c8819288,-0x5382ec52049dd761af3e0719a885251542a8c3cef69da8,0x2a37b4720238912926aa417feca9dd457c467157f71118,-0x13441439a342146192f66b3cf86a444732903ed9f6d61c,0x7eb075b5c8cb104fa3e6a13b370f6e3730bd1080569c8,-0x2ec243ba4ea090ff7581c29bbe67e20760e92a7ea84f8,0xf71f3fb68275c082a50e3c37a9efa0f35278661a7b98,-0x48c17b6486dc3b10184d9eb4317268573d9129da64cb,0x12ffe9b87dd61613abe7b287afc15192be2ea5e62770,-0x46030dc07a26800ab079f308d5f21a2966d9667b33c,0xe1faad30d7e6019293455977e0772263a44b26c370,-0x279bf07ecca2af67157ccb83e64f890dd0937c260e,0x5f953541e1ee0f209b314c86b976f472fd9b049e0,-0xc429fc78179bec44514392321afa3489e064269c,0x151889c25c8b4ba9f4ee5929c6b5368478f78540,-0x1de6e71b96fd854c378ce8861b8d9efd72481f7,0x222695815fc3ddcc44a0d09e71820cfb561b68,-0x1e8c76e7a2c97114943fc6c2f355f153095e0,0x149f16426cb7402198a5df7e4129ea8f8cf8,-0x9fcea68b603a7ea63c23f2eee9f012c950,0x33b857c723a78d53c194be45ce2c721c8,-0xa0ebfd760b83cf8c54c0209b7c6d750,0xfd77868a699c6b823dad6d59520d8,-0x93c50cc93b6692e52d5d357eea9,0xf53b592ff88a845daf600000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 26 52 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 52 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 58 indices rho q7 m7 7 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 58 indices rho q7 m7 7 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% []
def r8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m8 : List ℤ := raw_ints% [0x0,-0x2208f1fd1fadd40132623a3ae792c6fcdc8e9000,0x4a61a65c1d03b2366cf255e8a3aedf5f57639dc00,-0x4f234900c60c7c07e574976cb6b48f439ba1779c00,0x369e0eb4c48aa416909da5b7015c62be8d488e2fc00,-0x1b7d13bea41bd97205fb561bdfca2dcfba6a90932600,0xac0ee679e4e9c6f3e318dc5d8908a5ab3f47845c1ac0,-0x3674e982b214678e735056c82a480e2c439fea721c400,0xe54c0d4ba68a05551b6d6e90c962904f4b3966c731720,-0x332cc63e6afa0accfa9f0de654eece2ce2037f05b17600,0x9d4b0f345d95aef41d7ac7c3d7d096a96ea6425f8b9e50,-0x1a4eeff596897ae12e5de7bf08c3b2f9aa526d87a678780,0x3ddaacd099a90690f91a4baee39c482517103fa014be3a8,-0x80b11286b2e1c6a1f4c24761927f43e1343ad5efc126840,0xee52744a9d66aed741dc3df75159e4f397a7f8caa7be350,-0x18ab0abc090cd7c7b254552e99e8345900bee16f36594640,0x24ac9a45b8c723d1931b5fefc30975c6868ab55fcd0ae544,-0x31189d83b721cb21cf3a4dc23c20efe4554a46a8a3d15120,0x3b53899e6c5d4b5ead6636f8e3afe9fcd926c9a957afc154,-0x40d4497b86a2ed6e255bc864c863b7314c19785e18e94640,0x40270726e63ac4e8fed7053b7e5bc19c1a8b63f69621dbe6,-0x398a5c83b59194c3c5a615f7e441235312b479f1541936d0,0x2ecd69c5e0c153e8117ff609982952834f6ffb59a1917494,-0x228686182f51ea14e02b449d1181f6de0e59d2c93037db50,0x17178cb4dedd10b60e55bfdc13f9b8c643a85f4843165df9,-0xdfe6b6e07155f5fc74006421dc51154151211a8cc123788,0x7ace162dfc7492430979fa84e72ca9a5d217aa4ea31b790,-0x3cdf057d64abc8053f4f733cf819d1046b9665fb4ef51d8,0x1b36f6c75fbcb1bd9b1a02944657d1c2a8b43e657778904,-0xaf2c1df9dba6941d5ef278f2a8b76d02a4e7d98f1f83c8,0x3f3963fc4703f254174b5fd15aa5651c7ef6bfd1758c80,-0x1466998404d066c6fb0b4352bea97044184cdb84152558,0x5dc49d4aeb1edd817d934893798acec23d0d4b7b792b3,-0x17dcb17707d8fff0ef1c2e3c1fe445b0cef9b244bd570,0x55906a060adb9699ddcdad9135153adab0b3034fbb94,-0x10c52387d709fa3334a308ac0dfee2955375ab12d3b0,0x2d9c83931185ce2654245995b1ed1e38aee1595a226,-0x6a87b207c2a1bbe251a394696d4f895b76ea36a4e0,0xd31e65136f6e5179b17fe72d22f4fa09dd14e0454,-0x15ddbadc7a2b8877de56d8e9248df99c2d043c280,0x1dc22fc0a154e5ba8d64b873ac36cbe9c3f39d0f,-0x2083fa449bcbe824749e3e5573367082a667468,0x1bb576a184e16fca2539b21df3015c959a0138,-0x11ba770b9c10312686123f954620033ba7838,0x816a865b044e127644868953eb8a5bbc228,-0x2727df797814dd0b21df8c444ad31539c8,0x70d2bfbdeba3794e5238fc426297f488,-0xa2a44ff8aa428ca8bc1a189bef2b18,0x558453ff2eb5dd80b30f1bd12501,-0x7db08efcf8029866539000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 26 53 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 53 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 58 indices rho q8 m8 8 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 58 indices rho q8 m8 8 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% []
def r9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m9 : List ℤ := raw_ints% [0x0,0x4632731a1156854277ea98197d9eba6986e609000,-0x97eba12b75b7c4d7f65148b83e599cb4a43d755c00,0xa008362ffa2430c0bc486ab788f6b435255896fc400,-0x6d5439f829efb146ffa5672f9a1420567ebc8ebd1200,0x3674b05cd3b655fc7a748eaccf27d50cf6a8d7b6d9600,-0x1514102abc844b9d03c12931f242f29ed1f95a67249a40,0x6996e2d0d2ddb893970208f802ad1c530150c6c606b000,-0x1b7b104f46d6f95a9cf7c6bd77efd342a9a291ac5fdd3a0,0x6105e704b1d4043989574c0cfc87c3cfe2e8300a9918e00,-0x126c45bb2f72c20c76d6159bb89dd8b67d7ac89cebcee330,0x30b7d54c01abbfe9f17f7e5c92fb51cd02b3efc4eddfec80,-0x71270c2fb4963130654ce25b963c71166781963a66527a48,0xe87deadbb913e1780d96d4a3805f558a732c9986d058a640,-0x1a90ce04c6d5c1e3fa6540f57fbbcd4f16468607e074e62b0,0x2b6b4393b9a8f7d3513c147c51f8c1adbde27a75802e78d40,-0x3fae6d2081e1434adf3fffbe04f9da4464fa8d1b0d2a655e4,0x5411be6011afe16a5551c15dc37704dee195c0f7b85fa0920,-0x6423383736ab251d955d48660bcdb065477edfb59763b6e0c,0x6bd15794aea940bb982f771babd425c1f76aebfb2bf4f2b80,-0x69133cf456cab3d75faeb814c36fe8075920af1179594d30e,0x5cc561ff6598c6f09276e006857c792264fed612ef4f5d050,-0x4a3d100cdbbc977c7e651fb07009b3115357a5e5d2904028c,0x35d956b2072f4283081a936b62f58d7af1c86880659e2b010,-0x23647e1baafa3f9380d4120fa3ca344a344c10e21ec8aca01,0x1510143dde67dfa9d84dc28fcc92c8bb9f268576aac151d88,-0xb56486b82373458c50033dba4dd574f45cf9c247dc7e8a68,0x582ae6b3993a2622af7a5fb698cfe03ca099f12a12d3be18,-0x269f4523734ac0d5b44d0a3cc8f1cd7ded41fe3cd437e14c,0xf35b7cdf03d1521cbadc1e33d379c879c327085acba0348,-0x55e5e5fbb989635f790bfa0602d8e2220ae255d27e52d18,0x1b13bc192f1b8b35f40d9d767d11b906aba4d8ee2e28918,-0x796ff9322c3522ad66231e0bd5febf4f9e2e0ab103a9db,0x1e1d6b84fb44717c2d18e000caf219f0e9fd5e685dd570,-0x6913ecbd341183384a3ac2239ab641726b395b21825bc,0x1401f82ae7f92e98530fa49124a3a6153d56b24672f70,-0x34c52177bb855d491ebadebf8bffa5e97a8750c2261e,0x77460a9a5cffd90f7c470aaf8b3a9b40a69e5327d60,-0xe43633ef9e19181df39e53363a138a3f18a19b41bc,0x16c2496080219bcca22087e81f990b951900bf8cc0,-0x1dbb0a34ccd59cc68a83b89035308f2a658023c27,0x1f1153b396fd7e66933554e2ee51b45c24d77e68,-0x1935f1548ac6a7bc5ed24c4c35b436167ff38a0,0xf47d4701a5197e350d5b1aae6e69da8e62df8,-0x6903942cd6fe7bd9dc976eae5f18c1237820,0x1daf05ad64acf08f1ec1fe822ee0d60da48,-0x4f27b362a7bf9ca77f553493bdef3a3b0,0x685f2184999367d95a64911110d0558,-0x3179e292e919f44904902e8889f99,0x406693f51ff5514814d8000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 26 54 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 54 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 58 indices rho q9 m9 9 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 58 indices rho q9 m9 9 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x1]
def r10 : List ℤ := raw_ints% [-0x54f1cf12bd04e516b6da88000000,-0x7f1272ea095b3d484b2bfec00000,-0x5aa8c58a87e6f43b15d03d540000,-0x2911e5db14491c885d5997860000,-0xd44e2039ac2445a6081ab43b000,-0x3416cd88b0c83fe04095e008400,-0xa17066246f775301dda13cb100,-0x195718ceb07d78d8cc466004c0,-0x3484cb018344757a2e6b8a080,-0x5b02806082980dd615b89c30,-0x851e3b4ac3644b56e0d7220,-0xa573be53083492dc773824,-0xaf87688d7b6d775160b38,-0x9f5ed622ccb8afcebf95,-0x7bf3c2e61bd13180409,-0x52861d42be381fee16,-0x2eeafe15d568017f2,-0x16ae7c9e111c35f3,-0x9436bc72c6998e,-0x32ab12c037e68,-0xe503c29ada8,-0x34815828cb,-0x9851f0e1,-0x14ff63e,-0x20d16,-0x1dd]
def m10 : List ℤ := raw_ints% [0x0,-0x90c80d65c3c272d91753d9b493176079a63a729000,0x1365a7084968b508cd742950cda1ab33492bec20dc00,-0x143bf6ce891336ad4ca4e1d999dd62e996a781ef89c00,0xdafaded64de028e9469e38ffb1f11c9af7235aceb7c00,-0x6bf75fb56917795844cd96ddb525ed7a671d0762077600,0x295b99e7ea91d2799f7b7d4203cdd01428d1d70936236c0,-0xccfb40e4bb9205c820fef87b0d34b3aee1c06f9cca05400,0x34c5292d8d519e028a0a1022c47e3fe3d604db1d3f656a20,-0xb83df31b71a5c712ba72a4d98e9c42f63cb0e16024a7fe00,0x22962a76451bb62faf85f796dd1a12877ab73bd0b7656a450,-0x5a656c6af87cbfd7683c9e2b6c3d17c1138f65c311583df80,0xcf721edfd924244597219546de43c578df31e238344d3ef68,-0x1a5024fd78c0539365327078d9d24d3eb8209e18f702666a40,0x2f8040e677c4488fca5216df13123b5f2a35432855e6f871d0,-0x4ca1b4043912a251a809309167aed528b531d98080d0b70840,0x6ee6004745f687909f757b442dfb47c61a60ff3de27818a884,-0x9066316139878393e2fafa89f08504d002e6b20e74d2537d20,0xa992c527b42431d28ae262d902826b7ec18a962c093e401554,-0xb3ecd2e66f54d91ebb21fbd546a10df9ca16349d78283b4640,0xacb7de0e0b08a9b616a2af9ab7d1a6cd1a9d449a7114625656,-0x962172181d7b6643814749aea9aad4368c4714db6feafa3d50,0x7637089294952a93bcb341401041efaf91c1bf712c94b3fdb4,-0x545344eee72e943653f4119225e5054e14420b5367576271d0,0x36787852a293622dec866e9011101e6542f6a76cd92ef06189,-0x1fd696ee5f48ccd144ff47b76fab2fe0e15cc3ecb381b35a88,0x10d1b6d5d5853757145b05f82db14598f428e3690dc41d59d0,-0x80472695761a6510c2f9eae653ac6b705bed45f1d64e0b4d8,0x370febab57c9eb6c09b62c2f784559a661cb5a679e9c3a4f4,-0x153a81119e0f85d5485b0de926f39d6409428ae78bb146b48,0x7540d6184b7fb753c1afbbd6ca6052b8ed1ed9998c8a2d60,-0x241beb1c24b1c593fcf69a0eca9d9be1cc883b18d7b7e0d8,0x9e059f32c0efea384816c47506616e122d04b4a8e6a2e43,-0x262ffc9901033a4f6ec33d1572a75a18ce988b0962ac370,0x81a72c7393ce2aa77f5227e70f917e0d201b054891eb14,-0x17fb6180f5cee6673752dabde3896cf6b915a2f2e4f5b0,0x3d54ef5981c8c5fc379dedcb93fd3848f9cfd37a24ef6,-0x86228395d79d7c956017949fa747507c09f92b542a60,0xf7bd600e8989d71b85b5266333283ccb1d9d5413334,-0x17c8992c0f2f3aa44f9be792e39c7dde0820b77e000,0x1dd04d823fd654ca89e934d025a83a60968680a03f,-0x1dc8d8cc05bf21dbe1b29010a7ff4737ea3afff68,0x1701638ee87778ed0531dbd81efb2191f43a2178,-0xd33f3fd5885d375495c676122de3bb8540ab38,0x555f42926f967478b5f9341733f33233a0b38,-0x1687e4dcb9d21da79cd11568fa77ec732448,0x37914494521e440b32dbbe029261a0a528,-0x42fb377f8778f81b5a0a9a736c985998,0x1c9dca31db2afa1a0b143f13495471,-0x20fcddd7f4ff582b16840000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 26 56 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 56 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 58 indices rho q10 m10 10 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 58 indices rho q10 m10 10 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x1dd,0x1]
def r11 : List ℤ := raw_ints% [0x9e468ed5ea321edb52b52f68000000,0xec706e4f00b1fc4a9d5a1f23c00000,0xa86d65a0352ff9d4cf59d646c40000,0x4c2bb083aa445335dada1f175a0000,0x1890473adc47b03fdd74428598f000,0x603a2ed777b8fabf324f27bb24400,0x1298d017958a4d1ac75ec10154900,0x2e95d8d2fa6a52d8f2c17fac28c0,0x6045fcb4e68eb7571bb9fa309c0,0xa64b5c83bb210a7043924264f0,0xf2592c7445e85f837f9550970,0x12bf6c5ec0a13b0ef5c1628f4,0x13cb811ea6e77ae51fcfc434,0x11dfb3e75ffbd56c048f3e9,0xdcff44c4950b58ebaf800,0x9204a856fadf327de175,0x5243799a854f32d385c,0x27546e5142565af40d,0xfd7b808f90853090,0x552556687af3fba,0x1780cfec75206c,0x5384f483a0c7,0xe755c9bdc0,0x1da4ba765,0x28cd084,0x1d40b]
def m11 : List ℤ := raw_ints% [0x0,0x12a9c9ba1e3c10cdfc01cf1046f6036fae6d88c49000,-0x27a2370475dffeb41526f318c34dad19c6ea9703c5c00,0x28f360cde0c54236bc705cba0db34accd49a378886c400,-0x1b6de770cec4f1cd86b5c68fa0a82fecd2f4d4aea6c1200,0xd63adaddbb290a1ae0f781aceced9d83cf7c7ffa48ba600,-0x513aa8cf9172e987492e2c7ac6902e4754c65670aba72640,0x18e685ff9f927a6575277d9b7114c52449a4c521db8b08000,-0x6579306b1bcba0b7d65f6e63677ec06bd34aba58baa4f0aa0,0x15e6ba81963e9210bb7988935f3fbd3cce94225d6c37e8f600,-0x410c02d44844fcac27eb064f5a43d7a99d6f43aa4135fe7d30,0xa80f265bc6adb9228bb66a26b7602d3c3332ca4bef0b36f480,-0x17d22764ba562dc7fd8b87c5e7f547d5994a7642d6980ce9308,0x2fc2ad62b2a2f75a5211028b06bffb7d848e3a297aa8d1b6040,-0x55260586cf3a1c4d8abccb7fa4c2ae6effb001fbdb2bd3e2030,0x879d4e2f925953ac1dc1e8b8ef63ace776e6beceb9925a82f40,-0xc1adfac9e6b335a928680483589502b153b2d64d9c79f639924,0xf8c71726eac300def83163869b6e55533ff6f08ef5f76840520,-0x12013e39bef0a89a3753b3bfe8d73aaa6a0c72b1e3c9041ac60c,0x12d44f88f3333d11b9daaad63423e276d11de64608b531c8e780,-0x11ce8ad1f68989f44c19a37238c86bbc6b3f64e444b08d5e5fbe,0xf3d9628665c98a5aebcda822db03eceb57b8b9ac4f6fcf9ecd0,-0xbcf61a33c84d6b3ddcdc41040d01bbcc781261a592fcddd826c,0x8492a4fb8e023aba4e7bb637646ac7f8d857fd0ff7bd5549e90,-0x542cdd1ef4f0505eaf9f526b8f62cea9a2f63f7248474787f91,0x305429b3cb506108be44f1a5c8bc6be37a1a4846c8a77a93488,-0x190f5ebf816957ca72881fa1c1bdc6c9ee4777ebab799c4a728,0xbb75b909c0b266748d178bf13f0cdaf16849bbeaa2af6d7d18,-0x4eda793c5178dd2ded0bc9b2e7f997ad46cd95a674ab5d9cfc,0x1dc3a973821907a056b875464664d16c9c4db21803b4e8bcc8,-0xa0cb4e634de8b9b55c87acd40bf0e9b9a45a94712b931e238,0x3060ce5a77b3d65de67d14a9957a2efd19214db6ac84cbc98,-0xce96d6b29889dbcbb6b1e15e1dc8422887d9f450437c77eb,0x30a656e7f52c771b6c320c2a4e8e1143f5aa22d8ad518b70,-0xa0b75aed91c7ad91153621f12ceda5e9ca8110fcb67503c,0x1ce07509994f82988f917d640ea138a216bee67e1558570,-0x4799bce1e9846b4879b4cb537d578c7c5f27c4b73cc0ae,0x977fc6e154b16eda1d6a0589184afe6ee9c493b5d7ce0,-0x10e0cc475cea0ffdb8bfcb2fc783e2f43644702058fdc,0x18f37da741f32e20cba7004c2518960113dd44ab9240,-0x1e0127cfec79d6e10c54e04775547887a482cd67457,0x1ca598274d6fbb68ae34bfec83d033988e92315d68,-0x150d4e852f43855f8422ce57339bcf6fccffc8360,0xb6f21a18836ce1a8d4a77f032b9b252c2bc64f8,-0x458663dc6a16c60f73a91bb0b39c262de11c70,0x111ef844df9e0bdc90ce0646689a776fb2ac8,-0x270781fc7934a1ff6fd483b57b8c6d65310,0x2afc7fef1d68b4a5c0c4d0a729f945bd8,-0x108beae12c1003fab9c276aad9ec989,0x10e46fabb6875a575c9600000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 26 58 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 58 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 58 indices rho q11 m11 11 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 58 indices rho q11 m11 11 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x1d40b,-0x1dd,0x1]
def r12 : List ℤ := raw_ints% [-0x9b4db4f2275b12035e415c03d8000000,-0xe7b4e94ff33f00d4f034f36b8a400000,-0xa4d3fdf36e655b6c37cd45f10edc0000,-0x4a6e0e93c14a5753afb4720433fe0000,-0x17f65373c96886faf274588b024e9000,-0x5db2e8450a49325cb6dd7fd75bcbc00,-0x12124c7a187db5e34071a56657d5700,-0x2d2ac316722e517eda4b827eb9eb40,-0x5d1ba7464d632586d9f07efacbcc0,-0xa0601c00a47aaa5e862cccd36c50,-0xe8fc46e8fdb7ae630b8bcf40270,-0x11f592121b432f0c521726c301c,-0x12e2ba995631730f239cba4574,-0x10f94b76c2ad900cb34f688b3,-0xd0bf3fdeaac3db9ebb2802a,-0x8910c4f4fc78e7a6f2e872,-0x4ca7521367e7f404e61a9,-0x2453bdb6c30ca752289d,-0xe7a6009636a7803288,-0x4ccb33d68963b1868,-0x14d8f70246b45412,-0x487e15524a619d,-0xc2fdb86a9e06,-0x17f8395de2a,-0x1efe9ede9,-0x141aa63]
def m12 : List ℤ := raw_ints% [0x0,-0x267e300fde5be2a8d7c3bb11925b671657c1ea1569000,0x50ffae7ff00e0ff7466f11274930ad052a43d777c7dc00,-0x52e9092cdd54e439c640e75962f73680e1617de5e399c00,0x370155d3e07ceb4dcea576f61861fcc324b1f34312cffc00,-0x1a96af2d656d1c00dc44c1ee45751c7ef2a7c3fb8765b4600,0x9fb2382ece719f9839d6e6e840c63b57747ce52f8de9ab2c0,-0x3074556857598e4a08f7369352d32f94e6784d18ab71d9a400,0xc364f453e4977448736d738c99acc77e01495f2aad57da1520,-0x29b8712a0002b2d56c53b0178fe1788b20b200fef2250ca4600,0x7a8c4dab04412251c8148a407c6f2ef4dc127872af3d80a3a50,-0x1390d3af79b3aef92566d422501b6a2c769dc8d329e1e3174780,0x2bdbc713d3ac44ab3bd316c0caebfe6e921317d0396ddcc8a128,-0x56e3a574a4b90ab3373355fdefbf26bae1838a8a7ed7ad85fc40,0x990371ad5861d67f48feeb5ebc9469812fbdde9ff5c6079a4c50,-0xf0a2774b36ef512908a5a8a5daa6706320287944cf2306ed8a40,0x153364663fdc12cae4889eb2d1e73f4e05f551d1b8ee7a0402bc4,-0x1ade47ddc5fcb1cdea6da346d6905817c8846f620bc4587249920,0x1eaf268ad3aa34678cd88392b16b4c61a6796e99b7140cb0e5954,-0x1fa20acec0114c81f6072d58d558af4acaa52e758d5e4580f0a40,0x1d79be5c96f5fb67a50c3f4963f4912053e5582b50b2813fa1c46,-0x18d81ec60021459fc130eae680bbd4d8fd13404f1f0316be617d0,0x12f2f29f14392e636db358f396c8018413650b9b9cb4cc8a9f5d4,-0xd13d247c9b18410a04ef9b1d8781bb9ccbb05abad0120094f850,0x829a465eab5780863dc78e31b49c56e69796695b745ea60d2119,-0x49aa156a83844de3fcd9a086bb80a405a82f03054f531ba96988,0x257f4ac338a7bfa7e880b42e97e3f8556d2a14e81bdc50fa2010,-0x113229d341f65e7f20649b41ba5708d7ce186955d74801008fd8,0x716c7b37cfd2509a321e4d4a5db2146f6cca77c145029bc6f64,-0x29eb679d21dae1473e8788480043508f381af85b7b2cbbd5ac8,0xdd8118d6caf0154f8ba6a4730f4f1754d06f602571e749dd40,-0x411cb7870fbfb72c2a46c9f70b18cdb64d1f0802dbe33ac858,0x10f51ef135aa9a2179d6fe709a1d1b7bc1b45a22ea21d672d3,-0x3e42e9d3e980bde72d572dd07c22f8805476ed6f4aec53970,0xc81f78f7b95e38becb10fffa821a1b333554b583eab79a94,-0x22ece9d9046fb2a29f5b2f4544a1729f7b7101716d3c2bb0,0x53f3a2c1570e344f990f589d582056dd9a66b2262064c46,-0xabd458242ed9717894fc1b0a4e9938e73c60800cfa53e0,0x1278c4cceaddc596d21848eb67e93683973c155a8a7f14,-0x1a4643d84921352eb38f799f0138d44169507fd54e580,0x1e4d158fd5854b53dee90e3ce9846ff9f5944740656f,-0x1ba354f682927c862e8ca6cf9284821415e29de2668,0x1350dc79aa92391b1038267e4656a4649fe10e3db8,-0x9ec7dd5676e29d2d2544551bda642bc9dc33be38,0x38b616acbf9875eb985669282c273a04ab413c8,-0xd0605292e291e91b03a3b5fbe11655c2ebec8,0x1b6d060a4f71d1822eb5a82aa69a95b1eec8,-0x1b962b95e7f398f021b293f3be1d83c418,0x99093fd34799175b90ded28ee3294e1,-0x8a5d39e3e0a2f8bbc99000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 26 60 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 60 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 58 indices rho q12 m12 12 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 58 indices rho q12 m12 12 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x141aa63,0x1d40b,-0x1dd,0x1]
def r13 : List ℤ := raw_ints% [0x6abbbe138488e79a80f53a5cd298000000,0x9f0f67c6f56ec4fa9d98c95beb2c400000,0x710241ebd6d82b29c1193dab29f53c0000,0x32f5f2fe506078d0c96c43515985f60000,0x1061c637ab18773883c5ecbbbbaa0f1000,0x3ff3ddca7755d1005d7344e26338c7c00,0xc4fe34a1aad22847cfd03ae42345b700,0x1eb5eef6b19e9abc69d0a1ca898bff40,0x3f2acad9a7f8b36fc32133495c12640,0x6c88fb5fd6a6827b0121aae69f89d0,0x9d3d8026c54cc1fbd85edca48f610,0xc1547c0fb32c00561bf715929b7c,0xca980bd417e3c11bb9a5c43818c,0xb55d42842c6d9310d04617dcab,0x8ac5dbba77629ff35c8ccd1f8,0x5aa523ac119a13c3fc4407d8,0x3262d67bad4c550a66eef9c,0x17b56dc549834ddf025918,0x95e78a476748df823ca0,0x312fdbd7104b6b94e30,0xd2f6fafaa6c4d31c4,0x2d204ab43d75b03f,0x76ea651dc34d98,0xe39165977134,0x11b44c63d94,0xadcdd236]
def m13 : List ℤ := raw_ints% [0x0,0x4f644320ba9d837c3d03b1d43ddc849e14fff2cc289000,-0xa59191f558fd2635b6e28ae973b554daa72bec670c35c00,0xa7eddf4e20269309118b48c58328d53cfff1b3acfbddc400,-0x6e5e8638aca91bb9cff2d26a6459b8f77c187892816831200,0x34d7484f57aa86f1c9239edbe4fa5d5cda440c77f67c943600,-0x13a449f738840edd2c4388c0e4f331fa2e67f3a42f591ca9240,0x5e6607d37ef7d9dbbc139453073528e6a9ee153224d175e5000,-0x178c196049f7fa44a472e22665b93c01c642107a0ecc6dafb9a0,0x4f98f311e4d08569cd65b0f0c2386560406b345fbfb8de241e00,-0xe74790a3431e76fa5fa8cec7e47b0ace631258d98da27ba6c730,0x24840ba0e3c3efd796c2f2ee3cd7c860aa117ed32419718cb1c80,-0x50ebace7d9e6d599d7065f753d54f33953f2ae58e3c40688eb9c8,0x9e6f5cca595e489d20b025c0e576ad4c7d33f4a98343a3972aa40,-0x113a47b8123a6acd7f7e8fe701758208e57a55806a5f8d7f6a91b0,0x1ac1aa3fc96741851ae774fe7193dc0efa280022a88fe393e5c140,-0x253c27ffa80507edd1776410612c9f33fde8c758b3bd27a44c6c64,0x2e910064b3c1a0865b9862a847330cef974a1ada6da4b42cfcf120,-0x3474b06116671ebb130a9ab9a1cbae82acba25d2d1872d5d7d3e0c,0x355130ffaa7e670211d632764f7598be14d248efcf714453f90b80,-0x30f54bb09e3a92cb1494b04dbb810ff658f72d0a9011e095d099ee,0x28a4ee8ca18e345e696993320e323333d8511163eb717028af5d50,-0x1e8422d86c9655026cd3550faad83b55e4d1e9d886aad490a0934c,0x14b827207a038cf93a1205c7119fe63673331ca3c7d69a803f1910,-0xcb70dd6aed051080c2ff499302cfc589c4c8393f809c454248521,0x70bd5e51e048aef9e3e9c07a3b84992994e583fd9d443eb593788,-0x38576b7c1d0a06e53b771f94cf931287d2a921602fc109528d3e8,0x1958a76c28a1f9564ebb0f135a6ccd69bf16983c11b383caf1818,-0xa3dc024b3c75745eb9c9e359f556c0a9e02f8a3b01184b1dcd2c,0x3b4c9243860fae6b8b6eb1cd31901a19dcf5b6bd104fee18be48,-0x1327edf43c146682dfe4d9be4929f519ea226e29b6d528622c58,0x5806f5e29b7990a64480c38c6814e21668735c94889398ad818,-0x165ee7b6289230bbecae76b0d4101e2ba30c92677f65fb18efb,0x50098bb8df841443c3e2f81cf189fa19c43c1517bd0cc3c970,-0xfa4b21f8ffb955efa34680cd1655338727f6d43b6edd332bc,0x2a6cae3d9ee2bd8115f9dc7cfd7e426ab7e1fbe9a3417bb70,-0x62d991c7973fc7c6685bc55cb831ce003af829bc3603d9be,0xc3aece8133b66d9513036c4f20fe08635c7a393622e2060,-0x144b58a35b33e70414a5a13a4aca264a26d66a97feea8fc,0x1bc4be93abbc3ba2354583071549a10f8e3615efa573c0,-0x1eb3da8673163edaccc52695a35e7f7d5be1ef3abb287,0x1abe6a37e638c34455ac2a3d0cf3cb4e356d92dfd868,-0x11c496b73347c31e40ebe54da3f069bc6e2dd3f9620,0x8a171174b549131ec98cc2abe449865553bf297f8,-0x2e5437c37b8c143ef7020484fe19470236cf8240,0x9ea7e2e5bfcf23ffd4659c6160e5a0bcfc6b48,-0x13479c9911f56c2f5d91a770cd58245771d70,0x11b3f22d5b08e7f6d5a094eb6bf45313258,-0x586fd9c3fe185000ded676c63d6ddc79,0x46d056792c9ae9578458000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 26 62 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 62 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 58 indices rho q13 m13 13 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 58 indices rho q13 m13 13 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r14 : List ℤ := raw_ints% [-0x39abb452c29cb8bdafb70fb0bda8b0000000,-0x55dae6080a5fd69d24b43312552ea4800000,-0x3cede1ae9875c6eca58094c4f094ab780000,-0x1b711b2189a20183175b143d6855ed080000,-0x8cf41d7bc1676feffda0a8a4ba210b12000,-0x22572d8a2ca4d7ebb8a00fe6cf84a54c800,-0x699b82bc048af7b51ab04606145572da00,-0x106f3d1cb3d6155c2770a8500706a0c980,-0x21bc97b72d5b8789b667d02249b8edbc0,-0x39d72fcfaae009620c579c26f1bf2be0,-0x5397e4dfe482ac1fd7667c55b74c8f0,-0x66806526f13e8f77b5264ecbbe6988,-0x6b16597774d62d6d701c85063f854,-0x5f89b7c726623f3d108662258ce2,-0x48d18e886b966f6970e6592c89b,-0x2f5a9d334de3a91037ca045dac,-0x1a30342e22880c631fdf685a4,-0xc3ff928d5bcfae0b89a51b6,-0x4ceab921a2cbc54eab05f2,-0x1907dfb79b9b2dace2250,-0x6a4bd48958556751de8,-0x167640db215955d7ae,-0x3a4be5bc1595e43b,-0x6d675687e915fc,-0x84b62249f2a8,-0x4e98c06cda]
def m14 : List ℤ := raw_ints% [0x0,-0xa3beca7380e4df303dd79ec5bf96d1860b4fe4c513a9000,0x15280b124fb4a695e346e2d925827df02f8ca9794892edc00,-0x15442d670f8329b96ce09226ec240586afb22389a46f3a9c00,0xdd9641c91ec9867403963003f20b918f7856b8dbbe2ee47c00,-0x69183b9046e9b5350c20576b43d370d40e4240f242d17ad9600,0x26b0c0ea79212a7e4b4e0681fb4e5543951b5c37584726dc8ec0,-0xb81e4918fd2db7bc4a12c629f943f8d3b59d5c5d4d53b6f87400,0x2d76d82363c0efa0ce53523e8eca8961b8d3b6aa1932a555fd820,-0x9817f3b9507e8b5d5fdcd03dabaf85c940932200de8ca2fc14e00,0x1b53ac31c26d160ee75759e7f81a8fb9c57e9d8ec05b51afc3e050,-0x4447603bb20bd4942e9890b5b3049d726e7119fb385df367c6af80,0x959c54b6c9cdf31b2fe0ddc2e1150f9a0832e4a21147d878cda8e8,-0x1218aabc30219f4fffd59fa6fd2e7423ee05e45445f6bf2c6ea5e40,0x1f1c07f42d4852190a1480958d7fac778c5e685918510091f3b92d0,-0x2fb991005b796327da78031074ddfce43a1b8e2df8562c3349bdc40,0x41938ffd083802d29024a5a2e1038e0ede7bab82a1edb9706b80f04,-0x50f1191303292c8bf46297dbeafb12a9ef8735b3efcc1033029a520,0x59f39829ef6b1d7c7586f9e0a0e226247776d74393f36854f3f0d54,-0x5a280518f19bcf5d8a85e0bf19fb99a28bf6c25cda8c56a07a76e40,0x5197e918de4328af9648ef350d98983d691b01d5afe1c8a41a1c9b6,-0x42ba17833d2f03d76814c93b103191e23975e839e70469405c49650,0x3152f9cc395a6bd979a83445ed99d637951f13bf84021ddd5f904f4,-0x20f3820420dd594ffe355077f20d1a92bf53326e5cd213e5158e2d0,0x13e23ab89eba1bedcbf47847a7da78c192d5811bf5035f65262c4a9,-0xad3c3e3f7e1b91077d422fb461d1aed19a42e167684ff4bd352488,0x55010fad8a32b0e9e9c990326dd2469c6082ad5cb6516a99126a50,-0x25843f3d91f192f56492c5a6dc1b703dec7370b2a5f9a198953ed8,0xedbbd04749bf4a27e623b038d9347699978b3cfe7fda6075bac54,-0x543f5863584dc337e882ad7fb73dcf493f614d5fa735f6999a248,0x1a9f3d6ade700a1bbbc20f5024d6c89ee6103d1d1ae9a7ff74420,-0x77879a5047a75501fee2467e4a41452442edfe4813eff2adefd8,0x1da444a1d41c3bab141204ecfb386de69d9f7d2e08ab63542063,-0x67568a02566faa3e3f91097d9b8ffac11365949f4b72feb3770,0x13a64dd2938e5186ff00966630f607ade0ff1e1a9f8ebfaca14,-0x33c08e3708ddeca2106e44fe917b96a105f8186baf9cfd29b0,0x74df13960c610cb4f021c87944b95276426ae284b1cf9be16,-0xdfbb013df5256c2214825f5ded7b81ca8ded9ea489159160,0x16616c39324a73c2463f88362e875db978326b0ab1a45ff4,-0x1d7354f6d4dbb73b6bd9d2341a5be384861d35145478f00,0x1f357c5dd448947b65d50f655d81303c51930e047b349f,-0x19f3b2f3e20f82a23f82bf45f5a889ec18841e8a42968,0x10622983edfccf790361d21774edd35ed992f542f5f8,-0x7853c70fb90cc31990e1fee62af993225be8eed538,0x25e67de1e839b362ba1845d3455d998b4d75a27d8,-0x78e6ec326e134047fda843dc8dd82e7624a3948,0xd8ec80de8d7989ae226e6b8362d19f844e968,-0xb5c079c025af5918618f779d761db335698,0x33175b94bf3ff74837e6a1ac6c9bed651,-0x243b75a2477cd82528840000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 26 64 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 64 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 58 indices rho q14 m14 14 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 58 indices rho q14 m14 14 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r15 : List ℤ := raw_ints% [0x1a145c84225f0cb6500b00ff21e777d0000000,0x26c9c5c7153a75bb589017be56e5473f800000,0x1b7fa9a4982da44aeaebb764a1f70505080000,0xc5f07a66e9461b38447ca9eb98e22e4a40000,0x3f776a177a02838aafb80ceffbd9a78dbe000,0xf711333736538337bc40c0781ec3336f4800,0x2f6b205c0e4e5e98aa9cbeed8e655e05f200,0x75e0ccf1168210aabb8785802e5aa523180,0xf18d85b20a747113afec7c9acbb64de380,0x19d54786c118d20228108a9525698a6520,0x2541311647d3667e6485ebc5f09d98360,0x2d927ec577fbda75fb13900428c035b8,0x2f7bf7def18c41b43f3a9016e5f0e28,0x2a3c97c12c0fa55e27433bcab1a58e,0x20159fcce944d801868537c50c668,0x14c901aadbb0c75b6e4260b15b21,0xb71ee628131ecf70bacd4c5c78,0x553af5bcb8c01367e0aa146ba,0x2141242c0a1e7d69cfed6e30,0xabfafd7e8c9793aabc919e,0x2d47ee931915ea6ec7bd8,0x97a07a76bd9e5cf8956,0x184ea9e64c34514548,0x2cf3eb8eb759fa11,0x358519493a86c8,0x1eede658af3a]
def m15 : List ℤ := raw_ints% [0x0,0x151b9818e39d80c537f8cb777db2710247754c7d6788c9000,-0x2b43255922dca0e7122991c1f88d5fbf62121d8a25af0a5c00,0x2b1b4f4302e6d5fb4c93ba99b920f021529c20568d95374c400,-0x1bd21d509d01d43826289832afe2730e88cb1febdaefb4da1200,0xd12e3cbf93f17b5abeb5ce50bb65ccc0cfb6a6befc7be5d54600,-0x4c48f91df4babdc3ea4dbc3baf833b54237b32e93ebfa1935de40,0x16784db5d50b600e2ce00d912b0726215b22bbf623988a746ea000,-0x57e592a8bf7840eb1e169c562a648e2d9d35a8d7c927256d99a0a0,0x1230e2ad5ad525b95ddebd3308ac6591ff2b6089ff858df35870600,-0x33bf7d55953b3ba27cb2222e2d18c60d196dd07030f46df3ace4130,0x7fe8ace840c81198e43bfe82703e41f3c892fdfea960f78a2478480,-0x1152c889c4b2d3e14d64b43824650d39ef3edf5177dc38733a2e5e88,0x21250629267e511b94a16c0b6931b92d9e1b92d2f26bab3c9e818440,-0x384fb668015a5a4128099f10e072e4fb65bcf2085405be7a88cd1730,0x5557e270d5c5d2fc10b28fd70874938b12cf8ca078a6d33e8fdae340,-0x73cde8783d406e74006a205fb81fc711069c88a83feddc9718eaefa4,0x8d1944022492cade2e2ea4b72a2e36c95906ce943ebd4ff46ad54d20,-0x9ab7d9f0a43ca9f8819c7a5f69f22d67c7b599ce43235bffaeb5d60c,0x98ef840e71d25b825c3a21be45982a2243fcfef7068aa7a14fa05f80,-0x886fc435697f974bd8dcdc9d9ec0c6862a798b7bda06b3e438d8cd9e,0x6deda0a662f8ac372b52344b1b5da817e82a7806e3671d68a54561d0,-0x5002f2a93c5481a46172e36b62c11b7bce19888d6255850c004ded2c,0x34998af3ce90f273adb20bddf9b6e74537da3f22f5d235d950822790,-0x1f36af6c9b4e6adb6d1ff49d5e7b51ecdf22c75408ed76a4e136e2b1,0x10b3eb00fb6232a9bfb3af9b6b59d6bd09284d2d53a825e8bd1ac688,-0x80c480e45a4a4886345b564a8eb7b3c2b75c9e1d9968e4739fc10a8,0x37c28e8c5e17d55cd81efce9fa0829ec6e315f14370284cf8009718,-0x15a5cbeff70d0e9fb79cb24201798d9234e6d74ebc3c3bef40505dc,0x78338da2b19a19eb882fd3a922d9183136af31cfdb418175daa7c8,-0x252824157bfc7cadd5bcb40fa4f057c195b53cbd420cd5b47ca378,0xa301733a262ac6b2bca11868335d3f21ef6cb3e36748fc5336398,-0x2771e8f6d6b8dde0fc50713a7e040f16803198422ef87b74cef0b,0x85fe30f5968c948a58c957b7aa2ece6103458f72c95158c14f70,-0x18c93eab093e7bc3fdbdca07eabbc3a3839c2a5b494686b50d3c,0x3f643f14e241c785567c8f03dedba9e0fc7a90f77b18b0fe970,-0x8abb902a79fe45f24dd5a4b772b23478b2d5eb49a8d391e54e,0x100c85fec62c7c3e13bf3a04ecbd57e3188ade71881900e7e0,-0x18c5698ab03167ac2e9b7d5b1015315e2a0d1146b64d3f51c,0x1f571366a9da898cf04f1ed679adc5ec30f30ad309000940,-0x1fd23e86d9c4058a06804d2c226e476b8c9fa0dde971eb7,0x1940768e48afe591a06c926b908e1d2a9ca26e189e0f68,-0xf2433395e11312e1214badb4f067a77ab927016db0e0,0x690a0af68ccfcf5507b4290aa7d10f9a038ae6abef8,-0x1f0b9bf7a3ffa81ef1485bd52ecd9c6a379ccf6590,0x5c33ff59164de954e60389a97d40106798653bc8,-0x9896225a337fe6aeab524b2e69f8add767ead0,0x749d3089eab7ce1255dc8a2ddecb8b6900d8,-0x1d81edf4a078f6d66fcc37a0d945e24869,0x128896d505db744d92b600000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 26 66 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 66 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 58 indices rho q15 m15 15 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 58 indices rho q15 m15 15 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r16 : List ℤ := raw_ints% [-0xa43468f93ce1ffad86b380d8773907ad0000000,-0xf402b85e4312730b4443688046245a527800000,-0xacd3d325fa3edf7f703be113067f2b311880000,-0x4dac3cc22608d1a9988e5cbda0fe7ebe9540000,-0x18e082a7edc7bdd9342d0d5ce7492b5ae01e000,-0x60b9ca6bceff7d78f88031a0ee8e8c8d7e0800,-0x128a2116867d1ba46b02db2b969f8ea94fd200,-0x2e05636db8c4b41ff28d3bf8c8f0458fa6180,-0x5e27d2eacaddb6510f9bdbbef9e4fd39ab80,-0xa0d50ba3d1a6ec761e472bd6cc738ca4f60,-0xe77eb3e81d2782e9bf21c952f8b1855620,-0x11a93e42d75f2cb7d53aefa85c0ce9d0c8,-0x125bd4a07e92bd5bbb7e38d12809146f8,-0x104977cccd2f382f2b269737a8e9019a,-0xc55f78e4546e09c982b59d89b8091c,-0x7f70ddb2f63bcf3611c9265448194,-0x45e93707cd476ef22737349b5cc3,-0x20667a65d6775887c651ffc5a06,-0xc9476c366f65413c5f3296acc,-0x40b0feb8036a2c4d79f73060,-0x10eb948a78c0e2305de6a0a,-0x383777b99183387de6786,-0x8ed8a9cbec4dfb73440,-0x1052c2d0a04f229444,-0x1329254fda507673,-0xae0374d6a4cfa]
def m16 : List ℤ := raw_ints% [0x0,-0x2b88e9b35574d996c37123a673400914b361edc2a58a1e9000,0x587b9a0e94d71e807044786447040d7aba455cecedb9055dc00,-0x5768f0d5e4a1d70e91ffd95314e588011257a5572e3c61fb9c00,0x37eb4177b2df8905b0717db971f63024574d79bdcec822078fc00,-0x1a0aa9e06fb7d2f9f991d830c1de60aeec178f6227b8d5689e6600,0x968ce8b001e93cc6a6ca2f6c5ddb36b62d6e625a8f15bfdefacac0,-0x2becd79ed491a73d4b8eb42770abbd6a3467cdf4288209fa22bc400,0xaa276623d6fa7e966712401cb55e1fd81d7d563f82f9d1593a97320,-0x22dcee0b7c3262d168a02b01f2d11e0ed82a83a76c9c6c3913f71600,0x62281d9d33e30d5cd4efda3a722241b1087e5181f7c6ea6463a71650,-0xf00e9c7ac34d1a4d67687b03363d15a4e36b916db5d723475403d780,0x202899c7f15046af419080ca3b2fd29cc9a9c114f3f63fd341981b6a8,-0x3cd6df0a3c7a857fda9cb97e77674f98b4342c4f3d3bb6cc1981d1040,0x662b6ffa9dd0f10eae85244361876db170739360f855d5404cd53e550,-0x98ffc102efcc6b962de09d799c9c7bbcb3a4adebdd02eaf756530be40,0xcd0da5d46c8488c16650be2c4b8db415ba4d05ba9f6391de30b0ff244,-0xf6aa19c71eded3da42dd1f836f38653067ed6ccda3ad0813196752120,0x10aea63c7edf138bf17d2398961c21e3b8bfbaa393a2fbd926c720b154,-0x1043f27bbdcf6e0153825fc2660db54ff84b9437b627713a861d416240,0xe4e4a3105a7ab555e8edd165414066a48c860db6f8623031a7e6cbaa6,-0xb5b84d9f803a7fbf3f88c48d3b67a0b251bf718ea8cde8f888acb98d0,0x8240b2bd1f0d9e859b4e80f219d96b599a9af2f96cff060fddf28b314,-0x5445fbe4399cd08c4c065a7b4e6161353597ef0831be57a88ef5c2150,0x312f61b6aff298eccb4d32277e6a20ac055ced28e5383f04f0a66b439,-0x19de018cec28cb44891f26c73ef4fb6f5767f679a3a38c1c2fc97ab88,0xc3d6e5459ea8ad6cf9430ada9fada541666da9a2fee11a398e961890,-0x533627f5f64953b6af3dd5de3863bf69aea36d79ee9c49643b0f91d8,0x1fab62115916a18b575f891b2450565f13b12174e23b7bcb1ede9fc4,-0xac375dd7325b6c9b941901eabb921bce444052790f34d4d865601c8,0x341432a4f35bab99b6ecea1bea72ed23ccd31280ba3e3643fe16a00,-0xdf3c1837fbe335019517ed7a6f330f97ede1762f4adc36dd5b6758,0x34b6413a7be0451e8ca2ce03bf9e4456cf42dde6ffedd6bfd776f3,-0xae780384a06f12da0029473f64ff760b6d8ef367973ab7c177d70,0x1f64eeb5712645e8f3e746f4977ec7920e3f1942e8ef9a5917994,-0x4df63f887d34d112c3e01be90fcd0e63de33c5be025facbcffb0,0xa55382f31ea57ba78121cd3400b0e50c998cd69c36981228866,-0x127d1bc4c72e4c38d0ffb1b08b44155ca4ef5d91919c71742e0,0x1b83853a8d5043792dbcdddf04c77c495649f3dc263eb7edd4,-0x2175bf589dc3c3a55dc2fd8d68e339434374f777784b46c80,0x208a9f376e8a48a4726019cc9960bee761fb9cbe556b95cf,-0x18a25869c295e0188ff231e8c41614e0f6cc9a351cba868,0xe061c4a22ef8931bd7ec1e7c6c84320552588731b6a38,-0x5bd97689833d19e1fdf18f5cbef5cc8eb196b9e36038,0x1975eeaa553212924a13f40c4ad4596c8c5775d9368,-0x465d84307c0209f4b05f86a8db2fe20fea64613c8,0x6b5b1b2531504cd5cf6b859308dc71186544d08,-0x4acfe6a2b916541f3df78fdd44c8e0186c118,0x11097a8da1e039b933fcf5182bdcc9108c1,-0x97a54d4f8bee9836e39000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 26 68 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 68 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 58 indices rho q16 m16 16 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 58 indices rho q16 m16 16 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r17 : List ℤ := raw_ints% [0x39bd8058f458ef59ec1c28b251fdbc1c8d0000000,0x55bc0ce8592a3a8eb8825b8a4de8e239cf7800000,0x3cabece697b10c523185e42395f8282b3ac880000,0x1b3de45bfeeee01900748f8688fefdb42af540000,0x8b7533ead9e46d613bda47049697eb844f05e000,0x21da2b92d3a04cee1fd77b3fcb919642edaf0800,0x67b0f6c5836d46291c32c15a2dd1b1f3652d200,0x1010e861145645c9ca09935c4d2c742495dd180,0x20d2a14ac17ed3634a7a522816eec8bbf85b80,0x37fa70a3de117bc9de9be3d3b2b5a234d1b60,0x506f07ae956acc44109bb9e0aad71f78a3e0,0x61fefbfc543d6b4e118351952e2127a2d08,0x65a7298013c04a19ee4ac7774e39112de8,0x59f8c7c443e3fdf6a55bced947a8ab98a,0x43f7e319444df0d144088a618db7d4d0,0x2bc24d91665bb80f741e0cfa41a2d60,0x17ed4d0274a09fc28caac1199abbd0,0xb0c53a886fdd14f4b337891cc0fb,0x4458b9fdbfcf629c8ca4b2401c0,0x15dc7f33a170ce2c216f28e9c4,0x5afaaced90a3c04b439cca48,0x12c51c27b4a5e526d703494,0x2f54a32ad371c0f2ac650,0x55bf873874d1c6e69cc,0x638a8925f2cd21dc0,0x37badd45401ce0f]
def m17 : List ℤ := raw_ints% [0x0,0x59ca6201e04100c6f31959874db412bab1f9fa61756cdf09000,-0xb50127cb8cdbd4309d2aafd73f394bcd202f0fa8aa4d9b115c00,0xb14fec0c29f630ddc489bc8b7cd6f3912040b022d92a3ff4bc400,-0x70754f6f763773ea71ca98df921e80cae3e893c00c53c970d11200,0x33e92924d9f9974c70c5cabffd4744a66a7582fec82381ae61ad600,-0x12963bf9d2055cccf3e037c2e3cf233d00ed1d275df339d561000a40,0x55f633db98e505e9901b723dc25dbd9b3bbb1029f46a38c2481f7000,-0x149d06d740a7faeb4ed980d1211e30c0ab55921df7514b63587387fa0,0x42e9b565543f6a9957a5a4075efd96a1d2d6387b8d48338cdd37fae00,-0xba7dcf00e0d45c8fcfd7d7376f30ae4aa5c6374373512f0d48ec36b30,0x1c35a76d885684298541f2fa2977fa54a16dd4ffe07ee3a7dea6e6ac80,-0x3bd12951201334cb5870a473bc0d4ed1aedcc2907d6db385c4bb3d7148,0x6fea8738e3983bf080e2d0e30d091ab3055ce5deb2e0aaddea372e6e40,-0xb9ce0999cbacfe92e1972a1fea4083d2c4f3e11679490a3a2422c710b0,0x112f8c0bc9b7ff87956e59c92ef7e7c3a791b3c45164f98c9028c169540,-0x16c0c2a423cd994112499a42dbb684d776acc97b53571bb98b9b97642e4,0x1b06bd16f79506496233909c6cdd15179fe1ad8b349a5e65519149d9920,-0x1cdd64d8cc2b7f0c3fb5b2bb72934ee2e25465ac46c802a453397f58e0c,0x1bc3ac1383217d6acf0920543187f7fafc487d75702f515386c01958380,-0x1813f9d2e42b3f815cb368b9cf866aebf530dd4a617a1fd9371f9c5e6ce,0x12d696bf2ae507031cc6baa4e1ac96a55b0f0f5cc91fc3a85b5d8f71a50,-0xd4c8e355d181bafa3041b64ee6c566f84b60041f16be4cd5bae326480c,0x8782433e616daf5d7e8f79355b15f442efcaf3160ae9264f9e59648a10,-0x4dcb097f8cd1ad19af69e9be59de0939a1d5c25d3e9a438834d06ce041,0x2836a59a774220d272fd65f3258cdbe82239a32045ce3b2564f2fa8188,-0x12b04004a6e3d0890f79167fcfc5eca9955e2ebf1febd4308e2c10dd68,0x7cacaedadbec22b2db42f6585af7b5b0619917d3dd648cdaab75d7a18,-0x2e84e2a4026364eb9619539dfbd2e7d3903ae78bd0ef08a50592b3b0c,0xf7c0da9b65ad7bdf508e6cb5f913bd792bbe61d85deca8de79d7f948,-0x494bb2eb61022a1d1afebb87e88f314100eb9fb8cf034e72ed475f98,0x132fc5a30e8ade687cb0791fc91627511ab60a73aa1cf3b66796bf18,-0x46bb7c2be95b091caa221e2f611f331b39edf0d031a01edbb94181b,0xe41a1ed167468ce21c8ed5cf8760886f6a09bef72e771e1e03dd70,-0x27ecaad95aaee4a9ee4bbaf98843bfefd5e8fe825fe5b7a21f1fbc,0x60421f476b3621508161be18015cff96a7973002340d0d086af70,-0xc5c428585575db3206a8096c95108aad200bab6a07d01ff5b75e,0x15606dd174afff759417135fb647d04c109fbd2e6402c48df360,-0x1eaa10a67ba192e97339d093b92eb48c9f4ecee42a90c55dc3c,0x23d5ee3a69c5391f056842585b43937a6d0201051acedfd2c0,-0x215f555ead2950c2bf211a6cad2eff26e65ebb6d7fee920e7,0x18174a41ed93ec8213e10ce7a86069bd75af9f0ba3a92268,-0xd03f675a167be9aaddd02583261ef4f25b9fc2defb93a0,0x5071a07b99b6a584108f9c71265dedf1d90d63c3d99f8,-0x14e75895b0a269cd6c01b15a813de3b3f8cc626fa260,0x35bba82ffe3977649486499dfc4656b909b6e45c48,-0x4b8c0a14acb519293b29b5cfbee627f5e3102330,0x2ffcfd4493d86aac75b2f9a05e7df017452758,-0x9d5807ca72ed25f38518db2fbdbbdf17d59,0x4d87cd3f9a9620f9c5d8000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 26 70 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 70 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 58 indices rho q17 m17 17 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 58 indices rho q17 m17 17 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r18 : List ℤ := raw_ints% [-0x127df499346f68db0d1095bcf98bef3183df8000000,-0x1b6ffa6cba19031458083bd044d15a10b899d400000,-0x1366b35f9a3a7335802eecfab0ef3f58244386c0000,-0x8b426f5bb7af1455d36a45d727d3a29d0008520000,-0x2c83e2eaedffe39bc30803f8b339b5c52a81435000,-0xacb768b8f118ce42b0ec5a652410cb3fd2139dc00,-0x21075a6c9118e672dc66d8cf84d70fcc90c4d5700,-0x51c848cb3d082ea7586d9ebe8889706931dff540,-0xa6dcef79939d5c47c177cb7f21356546d1a9600,-0x11c2cdfb1d606f52fc5d70d806896f573b76b50,-0x197b02b90217843e75d597c0b0d3d613725480,-0x1efdb282e2b029105fe2fabc963dec2d49e3c,-0x201647cff7c354592f20688b7c0986e38240,-0x1c574211095ddb1638d7830e1c1ea078153,-0x155c4ca1bdeb41060da132cad2006898ed,-0xdb78edd1f30130573655ab323da721fa,-0x77a9707c50cac0eee9dd122061f3226,-0x371365720892b3c5a27e2ce003d955,-0x15379eb5c5b6b8707280df566fb16,-0x6c23185ded4e570934dd7bbced8,-0x1bfe7c258fc931ed4ef36b0d98,-0x5be7807e2ab1cd04b348c0ad,-0xe646ece73fb164ec667e55,-0x19e12a4a4b88a45ae1192,-0x1dc658f7d9e695f7a2a,-0x107d858b3baefe77b]
def m18 : List ℤ := raw_ints% [0x0,-0xb9316a23de86119a556448a7104366a10f13946902308c029000,0x17256d62ec645b033af62f9bccbe80c571261104bdf400fd3cdc00,-0x167cfeaacab4494893fd2e891daf17a0c38b682d402e5b4467c9c00,0xe249cc2436780963f19389327c99571e0a05ac084c08cb324cd7c00,-0x678da6392361db2b5c37846a5775a4dcfb96934da6e2298cf371b600,0x24bfbe2e5c456f8ddb071f697e30a798553c4bfa8b6c052edce3066c0,-0xa86937843f2b8d71d146c32718c01a58931b17551f2e4799249339400,0x28019797814e9784ff92cf0597fe40be229f98f7eb6008ac39a3c7a620,-0x809cbed7a22983064efc4c4952e03d7aceef3582ff36263c8350a99e00,0x162e5524319120bbc9cf426850b7df0f050997ef4ee89a11e55faf35c50,-0x35226f6aaf818178a42f763c65892d82cacf6500d904eb2998c1fc3bf80,0x6f7b5cbc68ddd3f5de6341e7239bce33c87d8be5974bdd669a806f2fa68,-0xce4ff1b8777ca3491621bc27967628a5005bbe8efc8448813192bac9240,0x152adb156a5482b44fb078f3f12afd1ec982d3a156751bdcb8555597e3d0,-0x1ef65781498a4fee0ba39e9bc63770e0c8e6db2fa6d0803239c33db7b040,0x2880324f2ee76b81354e6dd66d97d682207a45d36534cbc66c83c5727584,-0x2f82a2aeea883e3a20ddefa24e5708289dda9ac535a08cee33885cab8d20,0x3216f8644bda3b8fe906243ca7cfa79c9177d071c93a075935a77361c554,-0x2f899cc3381542ce8382052edd6808b65028b0330c35dced58bf28b82640,0x28a7bb5c377695fe0055bcae9f7d3806905691f318fe594e66ef3d1bab16,-0x1f59ae06cc2999df5f8ec4b7aeaf5f2f4c4081ca880bc2043cf97b2e3f50,0x15ccff2be096d1a969ac70d030a6cca69f771028a4d4453dfd9329b0c834,-0xdaac00868a8468b4a5feaa1f1479f92c31a067b2161ecd88f2c0fa413d0,0x7b7e4927c67be541dcd0c1155ae343b609e7acd651e4fa3f054f8e317c9,-0x3ec099c54cbf99fa22afd44d74abc614727f8ee561266f36d9f3d769e88,0x1ca4fec5adc62c3c595f9445ac447f88f88419e135d9cc9881795230ad0,-0xbb886c8ce4d2926a66f8df2b0cc8a97499acf6fafe10aae0776af428d8,0x449ac13982d2933278107fe4e591c847b83f0105cac61febea3c802db4,-0x165dc79f1b8851300822815ed02b0a789b2d5c73f5f8932da7c6d2f948,0x67934458e0cc2bde9551d6fff9bd790b3458f9c6d1261daa1db4c96e0,-0x1a7e002e208dc3a7523d226e73c0d48ac8afde4a16fc3be83eaaeaed8,0x5f4c41dda98eb704c7e8df5bc0c565402798e5ae0d034dfec6673683,-0x12b6b0ab8f6867e92c66edd770d731338bbf082a31c6ee353251cb70,0x32f8f0c3c67eaf89bf79842bf109c73456bff6ca9b0ab107c13a914,-0x774df10b331a63f754d0c781e206142867e54127a252400c182db0,0xed7253b090aff0ecb181f2095e44797fa49e76c198ece7a332f36,-0x18cd84615b16aa81db7f2254e6928694bdb73a3a1566b02658860,0x2249db7497fb163c882f32ce913f524016b63866efa1352500b4,-0x267f1fdb8dfc11d47662e7e83318f9b827b63536eabcc47de00,0x22514f6ff31304e0c7fb0fa46b35a1b8281a2c6769cbc6d0ff,-0x179d80bf2becf4b10cc267d3f18d2a4074c4a5709bad6c368,0xc1a61c7115f51168ecfec0383adacf631b92502df96ba78,-0x468f3efb97c7f228a917eae27051ee2e5eb158d0e5ff38,0x112e0730d669cba5eae27ddad765a0be6b84d8e1c8278,-0x290e0efbca6c5796f0107fd9d150fc59f4128c40e48,0x352bb76e9e89a2d2d668030e565eff171151191a8,-0x1ec708816f50fdfc8ef4df31c11466c38cf4398,0x5acb888928364466fee3306980bbdc2d1c31,-0x27a0e78dcaa527e8a3840000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 26 72 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 72 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 58 indices rho q18 m18 18 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 58 indices rho q18 m18 18 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r19 : List ℤ := raw_ints% [0x578c3531ba4909926c0d346c56ae25be03b758000000,0x81cf785d5ffef3dd381eb576a1fb34080e04ae400000,0x5bb9011adcfcb33ad69d80097f9dff25a046a61c0000,0x291dad43059117ceca27e17058be0f39019b7ef60000,0xd21b87a09dc3a4b54c08fdb62d16530e4e8a5039000,0x32e7344292b4f96ccad358ecd6741c20d8b5c181c00,0x9b97712a08c6fbfb9059450832b1db914059a62f00,0x180d6f1a3792af0e25b59bc94e51dc4a35575e3140,0x31044a3fa84dbdad2f4621737d8cd6d871928a840,0x535eac909fb49c04aaf5ede236639b864857c510,0x776fc090922a55cfd8be103eaa3725d5a994a10,0x910ab8cad3912ed0b4bc5fd20406ecff1a20cc,0x95eac0f876490e6dba73fce4c4f94dc73d0ac,0x842ad56af3371e1f19a885c3896212e2e2d7,0x6368ebc8a05255f3e7b7f111f20520f88b0,0x3fb1392e8e025be50cf65c8f6dae474b25,0x22a382b36ace8457c132a71ac75ad3a84,0xfe5d613b991c16aece77054b2986ca3,0x61ae17b8447f1f0da4811f9ebd8bd0,0x1f00f3970646a65ad8b3639349b62,0x7fe557e491063c4ec9782eb34b4,0x1a1edef99cc87668f5135e0741,0x4118f9b52ec0cd124b33ce30,0x745359af4a5392a7e236b5,0x84da78aa47d48ade4c1c,0x48efe13095cc1d78ed]
def m19 : List ℤ := raw_ints% [0x0,0x17df5eae9faf4844e501ed5d8918b03ac2f186218948420c549000,-0x2f5dc01f660705089703201371792597395e8319c7c7420a4d85c00,0x2da6a743391809bc9991bf183d414bd67f2f78b74c9c6fb86f62c400,-0x1c7955f66fadc42e848dd30cbc48e6fcf7373f7ef3bf5b8f877e81200,0xceb86cb8645628062f2e302050b27e2e740bef76b02a5cf78c7c8e600,-0x48b93d01771c1c8c78bc870f334aec9fa2dd5d36d85a9bea9b55981640,0x14a4bab2a6d325d923b895baeb719c267634370508a6270c2ebf90cc000,-0x4dbda3575f9f675a145489226c754d0ffe6d6a8a5c4f4e6d0d81c3616a0,0xf78e5a9f657d3fd20bec457baa41ad3d8565c9575193fd175bba3d41600,-0x2a47363ec794104ec57543803775c2720b8035d97d9991c9c8e66b60c530,0x644256432f31bca8125e746a4b31d73718c486e99e9b9f06b01526f09480,-0xd02c363a1785b7fc56472054b6e32886e3031e068317be7f6d38ae436208,0x17d206a36e24d65f43c18ed73271d4b904c7baf91b6d49fb0a86c9ba1e840,-0x26aba9c26afb6631051a021767b695aaa5aa5ab1b213cc0fbddfaad52de30,0x37eaeadb68c2084f8077035043e7ee3db5924fa23aa0e6e4acb3a97d15740,-0x484734d33bd882c3e5c3a7fe15f3355da69ab72651ebb508cca823aec8624,0x53bf66c2120b059bb95ee8c61e3c7e196387f07e00d98ca43544cf96a5520,-0x572bfe37b3c8ed767d65ed8f84497ea34df5f0e276e2e44e1a7dcbfc9660c,0x51a37717c251ecd7c8f163abc765e5a6e2549c265269fbced0bf9aa5e7780,-0x44dca6fd4dd8a28fa297f0354c754cb3bf4809c358f78900d69e55aaa317e,0x3458132498f9cce5c217083d842fbf22fa0c6c3f43e1a5c1f4353202826d0,-0x23dbeff66969a7f793c95f542c2e2108b2415d7897cf24608158900c99bec,0x1621d65aa4ac08c0c9d829a2d7e3340df81cd1b477e3e6f03f90c53ede090,-0xc4c03db5a6e89200bd104883b611e84b09637a3a76fbb6a632a1f8e785d1,0x6249ba2e734cf34aad8feb857fffd28acb982d3f12199b2a9891a5260888,-0x2c1247d66d2ca5df44f9d6cd63f1ca8a3bf9e036643ddadd47986b52ba28,0x11b2ce7a98254beba149eb8930ac6fce77b6ac07a09c85b7b2f0a0002118,-0x659298539c3e086447193ef32c9b10f7708a39d6044daed1ff7a7a500bc,0x206f46eca610fcfb1c2cc299675f6116866591f8b56401fea07a611b2c8,-0x92f29b29dad47cc30b474dfd3b4c561b7579075d07b850646341f9b8b8,0x24b9b7fbee35c336ff07c8236027e42c3e329caff1bc3600f9e7cdaa98,-0x80e79dcbd0285cadfa93670b1f238781ba351d321988eeddd52f90a2b,0x18a92b6a9ab9552290f6f7cb5c125f8498e1a94069fcfdeda99a73370,-0x4153f65dea06798737f6f9e81a9da772e21539b93c00bc7ec9d7aa3c,0x946be949f23b0e329c491fcfec4415540ddddaae593482b3de0cd70,-0x11e1d50082471f5e26b33f3ac5609977a514901d733074723dec3ee,0x1ce05bc589b7985b4c26a3a2aad6e22d14f98ce93cd9e8b4cce2e0,-0x2676a795013ecf69bda629ed142ec7cc66557c4a5ab076ed2865c,0x2979dccc539889ec7a49b146e4385045ab1d648949789087f040,-0x2361b2ec6e2fb6fc41104944716abfa26760d700248eacfe117,0x173369df413bb737bba7f2109411ead31374c8eb27dcef3168,-0xb46764625350a6bd5f7dfde85a9a78e9bd633be1d520fe60,0x3df9d6a5918325c4d613aa4a852bc223bdb022343d408f8,-0xe21eb231e6c4571a2427b2ab8819ac9c5f146241af4b0,0x1f6234db5d9a67acd4bd4f2bbddad269bd3eb47f0cc8,-0x256d1f391ad1d1babcc36f90802cb144ca7adfee90,0x13bc6f4f27b5246f8a02028d48dfe2b365b7a5d8,-0x3460ddcae1347c7e7169b2980d0b67589eb49,0x14402b0eed84f6287d5600000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 26 74 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 74 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 58 indices rho q19 m19 19 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 58 indices rho q19 m19 19 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r20 : List ℤ := raw_ints% [-0x18339ab63db29ba3714a9d609a44e4bedf200fe8000000,-0x23dcb61d3e3668b2d26e8caa78cbba52290f2d7fc00000,-0x19529b668f7e25ad38f2ca9aa841eb743ea30778840000,-0xb57cb7aa0c85342ed58c90712db9b9fbdbcdf70f20000,-0x39eb0ded131c528755a2d298273ace83ee5a2b933f000,-0xe051d62a11e1412acedd9e21e9659de21f129356a400,-0x2ad06f67df82a08f965a97d9a36dbc113623690fc100,-0x69ca6237c877dc7168db3cae05fd7642543593836c0,-0xd75b852fde931b070535ca32b5baa0e110fb4a6540,-0x16ddb6db7cddbe0f2d949085d7d6ef36297d667030,-0x20b752362d71e5bf551bdb499c5a8a71e5539e290,-0x27ac9a17217bbfdc20ac6e10687a7822ae2a8f44,-0x28f1e3ad0c91a9d4688ee63d7bf31000c75270c,-0x240955e4c5ea8436b5d4011055228ad76972c5,-0x1b0e0715c1fc2d41e8a0f93ae1a988e1c454e,-0x114c7d4b15f837d6a16aa4e8ffbe20d6802e,-0x962fa8be2c0a5599c2b4657657292cd2ed,-0x44c1bbb432aa0fb5d5b275651bcea472b,-0x1a54706886dbff1cfa7a23c1f727e0d0,-0x854b61cbba5de0b80a9c0fb59303f8,-0x223eb58a6258e4b93accddbcaedb2,-0x6f7457e06d3b0ea30b41ef7b26b,-0x1147e3dffb64c4c0bf4a8518ba,-0x1eb7847f9085310993879bf6,-0x22ddb5d2d6107be80ac0ad,-0x1300f72fe00d6e7e7955]
def m20 : List ℤ := raw_ints% [0x0,-0x313cb3482959850e1853f990eac2eb79321224a52b2508396e69000,0x60f279477f5e8d0592452dec506a5587e652ee652c0af8353fe3dc00,-0x5cb44499145d58f6b8ac9660c16c397f8f53cd905ef8802b62cbd9c00,0x395b5db32f4cd2414d1f2cf445dbbcb6ae1f71bf57287d070eb8e1fc00,-0x19cf682cd1e0044faab85cef46e42ab69b5348f6f427e326842da1b8600,0x900acd042521bab70f339c74b73e198e8b990fbdb79853beea1f59062c0,-0x2887a6e7eda816a403506762dd80b930b99dcd1169c9d173c2760b33e400,0x9740ec30a6c5607b347511e0fc9c69d50d3854d1c702ec91537cf7813120,-0x1dd2bf93adcf243aa366c0707b0bd9f3516924f05cc5c3449147ddd16e600,0x50b623de39ee37c593852a96a8b27bd0d19f6b2613519db1202b81e3c3250,-0xbd8214fc334c91f357993ba0d4ca5c90b7f1a1b2467801fb5cbf205b86780,0x18577d42d2fc1d3a75149096e999554e62e1e85a1591cef5793e08e4ed2428,-0x2c1869932d3242a2b6ea5de0f27e0ffd6f6b51c6c5ebcdbc9ab7fa5b9f6440,0x46ce01fd6533fa1ecf28ed06833986e593da9fd9751bf8e16f1b8741ff2e50,-0x653a71fc04a6f0cbcc3aaa8d4bc21ae8814dfd6f72e6cda0bb3ad8e90b3240,0x81510d48decb2143a441ff216d039647895cb1eab5882e24be6de0d5d538c4,-0x9405985fa6c60dcc4f4cdb1e47e9cbb440efc80d0702fc98de4647a88d6920,0x98230e9297dff7c4c87591f4a733c0d19e50a0115f90840f5b78e2fff8c954,-0x8c9e8902a21ae615d41a8db000cf0f4cb19d10b7ba4f7d94bdaaa8e3043a40,0x75005eaf851c4812c0b0c303c0eb829e162689c7042541d5f6b8b147123706,-0x57ade18c8f299850b1d4c0a3b16a940a364164b2ff6d6dfb301950bf39a9d0,0x3b2e60fa3cd8407c600377ee9186537e665d42e2ba15dc927fb9167f5ccc54,-0x23f7065876e8a54f8210686458dc0c8dc232cc0480f7bf7a4aeb8a2bceda50,0x13a95d8a368fab0eee6060dbc478a0e3fd7d75f216adc27db36c60ba76d759,-0x9a82c6e7357aa8038e22d08911f39d32438dbade2c34f8aa8933ae3929d88,0x440f7cabcb2f702d012033d78ca1c7197c1eba71b7242fcbe3e916b0b2110,-0x1ad39b062ff8a396be6b43a1373923040875997488b99a5f286094bede3d8,0x96f6f510bb6e983fbca59eb46f83d13b5c3f6360e1ba96d5c87ceae25a24,-0x2f3801db8214306bbcd6522fade6335c76e1b2025b38643cdba42ea408c8,0xd14c97bc30d221b7a7924e000abe03e40dac4bfd32d1bf007a25933d2c0,-0x331c65f73715f1df75502b5029e7f5647919a1f5e2030aa07287c8d0658,0xaf0a97fed065bcb12cc5f1f5c3c0e330b141541a88dbb9fbe0dc889f13,-0x209f6e4d1a553e83be287fd657d14a9a8e1b5514400a976f11383be170,0x540a9279929a0ba29cff096f2bb2724c06c03222446c0b4f2c13b5894,-0xb95180de4a6b926da8dc420504a7b834d52aeaaf84343c0b091af3b0,0x159f6ef71c73a8647ec3ed7f5ff7cf7f05f586594a45cb2398b35686,-0x21bb02e7a2afbdac3840459cd28bb5dadf8bb59ce0453d9fd3681e0,0x2b47b349fb71370fe6b61cbf59c1e3379266290eb14b4dbea8b094,-0x2ccfd9388eeabb5528a83fd0c7a2424da48ac7956ad3c88208380,0x2491dc9805a11269592910d1bbb3b6c059c1ced22822f078ee2f,-0x16d7a4e109b88ffe9ec7541079d9df383cab144bc575e869a68,0xa85b1787bd889611893764a6a9db4e51e72feef15bd4a06b8,-0x3681d99491522a022a5e8bf4a91dc7a9f6254eb5a28b1238,0xba2bb7a18b0759c6308467a4dfed6caeb9e2ff293c8108,-0x180043d84c1038f7b5b805d189358edcea0a90e90e8c8,0x1a588db37d55c657ebad1a55c3aec09445dc5236f48,-0xca750e9dc7b24f113eb5d0f709cfe1d415765e18,0x1e353ad6b7e8bdd51c178a16e005ac4b6800a1,-0xa588c93ff9e576d7a19000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 26 76 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 76 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 58 indices rho q20 m20 20 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 58 indices rho q20 m20 20 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r21 : List ℤ := raw_ints% [0x64e4463958f7ff2e4198afeace60ec09af6f0d728000000,0x956a59f38edca44ccc55200131585a39c8783746dc00000,0x697017cf5c549d306b57b4fc9ddb58186e0e34b91240000,0x2f3291bcef353860e92e05df52ae9cddc29dc4a2cfa0000,0xf0d1cabb2f93b714c19f46c466efd53dbae9120ab77000,0x3a3f87ef6210e905ab4bf4eda1e6ce73880fe0b35be400,0xb1ba1a02daeb3e7afbede2f6172ed2ce1ada6c3792100,0x1b6bedfb55451a40cab95c073a7463c9776002d9092c0,0x37c4364d72c4ad46a5deab03670c9958fd3684f193c0,0x5ea2be268cc5c618c8e53045a4fecf3d9b1fc7426b0,0x873e381e4f60ad55327d0359ddf290186053c19470,0xa3cc1be6474cb866d70846ce335b74e7a519cc564,0xa8cec9d876dc90e5daaa1f143359cf7d35076f54,0x945858c12e8d6e6dd5d3f12d9e5b4584de7e4ed,0x6f2f9c826fa8c5f40ffa197b7dbe143af68788,0x46f63696d14ac69c851c6b2a54eb0331f7080,0x266d6546eed21c4ec444fd3eea66f6a45874,0x118d97d963f6271cbda4954e7b1c441af3a,0x6b4835e4139949399db455265a41018e0,0x21d9c4ccc2ceb624de69ec58e0fdd538,0x8ab6f18a52d13c6243be51544d91bc,0x1c1e2c88c0f9c2d7937b55319d565,0x457a447e2104a8b25dec9c47c68,0x7af04b23af50081f2a413309c,0x8ad19e5b32166a3a3a6f07c,0x4b34cd3d76b7b2547dd4c]
def m21 : List ℤ := raw_ints% [0x0,0x658d31c4d548a26d122d32bae43205a9f7456b94a8fc60f673b89000,-0xc6765430f0932823334c263fd29c40684b0b0bb0aad69fedd3c5f5c00,0xbc52667010559aacec919ccc9cf46b12171082dd00bcde3b8613b9c400,-0x73992ce31cbfed74828a1ce5d7f383e2482215496694372a33f701f1200,0x3398c6d44769a5095675f5ff44fcb410e0ab8435d850c6c55bb1ae437600,-0x11d8cf6da8b4b4c8feff18888e70b7694f65bf1676ffd54daca85df250240,0x4fa8174277e8bc925644b8a21e6a05e58b256acf980575b2e8b77c1ea9000,-0x126a3a0f4d86cc464254748acdaa6129059761f2a066a54a8fb3ae011a25a0,0x399099c93d07fb607e27354742fc8f6b087cacf9519f5e647a02029f9a3e00,-0x9a5282d93f67dc84303808aa752530ddfdc583cf57339b6f457428203ccf30,0x166d233d58ea164f8b9ef8ed999ad6229e7a5e75d39265a7530797ecf933c80,-0x2da0626fa43e067b45a87afe444b8b60f962bd406cf6ec52f5a5110b65720c8,0x51cb5e0a20e5dd16d52e1bebd9b4a9349b7c14e7369a04181c976cc9f207240,-0x81ed54f5321eed8ffe5c02d29b0bfb1c21f47c8a221e45c9035774aca7fdfb0,0xb7afd2b0af83be2358fd754c9e4911b94ea15b2c1bb072d6f62e306182da940,-0xe7f29f60e0a14f00d02b8f59d22bf36f723c3d6978beb636e3627ee78d2d964,0x10651ea780dcc372e10bc365e936a101c96c16abf419299840529928b5740120,-0x10a42c4d8b87a51470785370abf97dfb92e2fd51c961aff694c53e9742f25e0c,0xf2ec3857dfaf56b6b15cb54dfd7a3651485e32f0df9d7ef9d758981a22abb80,-0xc7676c9e32442ab52a3d9120bf4c9298efdf055e410034a13bbafb5926159ae,0x93562d89cf4680e39eaf6fdf076024c4d81595b4d99031f4c923d25b7df2750,-0x61fea6cc9fda9c30bc152ea6762d8060bb3cd3cf142eaab4be56c8a381a20cc,0x3aa4a49c4b7b2d6b705095d2de20ed36748bec166772b95556359e557664b10,-0x1f8c2da4ee37e4f4a50ccd6dbaf923df2e9b9c62ad61c1862d48deda2cb9b61,0xf3c5598f5e2b7c9ad3f0d9e4f7b470b6eb118fdf56af22dc8acfc7b5c7fb88,-0x697ead9d3ace026bd87212e7e09ac3f53aa54397c52e174bc78474064c26e8,0x28d0aadcb90cc3bfc99fdfef5d2853185d52f7a056850b1219e25425016c18,-0xe13a33dfc14f2362ef851533768544e0dd2c775413364fee6bbbe27818aec,0x4501505ba29ceea2893e60f9bcb066b8dda95d1fcb5d943142058e5a6d448,-0x12b410c50f83accf21fc4e3d7c8c7fd53cc0a0bf9faba4d514c98c1b946d8,0x47678ab48b482f7b679e601a06b89115087a7328638cc050f2cc8fb46618,-0xee98d0eac7131f1f4d9f35a4f44ea4f5c2568e5c2405b60e0a72d5a453b,0x2b5143a91da4fd0159fb33a8779cf7227cbdcd381c02814e037ef751170,-0x6c831b51c9604b07797f2c5bace6b22e4ce96b5e150a698688e184ecbc,0xe835e4474d513bc0eaef2e5ca05d22da10086598aa694fd691b558370,-0x1a3c2412c31636ed0ccef37af7a76ae0a8fa6a0d5b7f691b81d9f1efe,0x2786fd22501a575d1aa2dd86a9d492be408108c7fc04d6f970045660,-0x30d85d7e75928bae027714f09c91fea1545eb3cb8e518e76082db7c,0x308c1cd931bd057e789a737d014f8c9751cfa92454754c826701c0,-0x25e3614adf8629c41cc87aaf371ba9df15ae2b8b6da2104274747,0x1688fb70e63653a7275f1cd74dad0eb621fe65af00d380cf5c68,-0x9d5e6ffdddfeceeac6b060321f4457d8235bf743a92bfeb120,0x2fff201268355e7d320ca8b3819587b1865a201bcbfe66bf8,-0x99664baf399098762c3091181740b194d7118b86359f880,0x125cb420f56230383f021d31d4150dab846f01747e8d48,-0x128bfeaaac099fa86d9baf90a369ddc12737b81734f0,0x81c7988cf011d2c12d3abd23903980962f5f0fc58,-0x116ab85434de1e9dee273817aca12f05e830239,0x548cf84869e6f82ed958000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 26 78 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 78 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 58 indices rho q21 m21 21 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 58 indices rho q21 m21 21 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r22 : List ℤ := raw_ints% [-0x18f45ce295039669fa65f4ced682c92ca42dca84860000000,-0x24efb903f747246c874ad8c4231e4a304daa9c26439000000,-0x1a0cba7cacd74183482a1c85d2b98bc899fd1e19b4b300000,-0xba746cf417522653abcaf64865890d0f50528f4618a40000,-0x3b6b84692b127b6ecee92d38b73d32af59c79343ea0e4000,-0xe5c9ad0d48c52220cc6c89fe2ffe1e1f1c4f114eb63c000,-0x2bc941b03a5eb5d2692f5c32ac6bf52aba25a86a675a800,-0x6c0042c6934719309f405f4390fcc13c58f55016620800,-0xdb6fdadeafee13e3042b927859d8b0a0f7970b74d9340,-0x17403db05d4b1d0b06cbd6880ae7a8c8bbeee8e023a80,-0x21312459b50c2a03e146a1076f000bbbd8c591ef5ad0,-0x282725688005f0f28f75afd6dfc2bd5b105d1162a40,-0x29541e1dded4ec81df58f8d9cbc38e63202a4c533c,-0x2444bb275e98e103b9347b0588f20f9630ecc57e8,-0x1b247570e39e708fd1472ee84abad925d600537f,-0x114b56318dfe30d5e6669f6d82ffbc587466b00,-0x9592260067f9236a60210b646abbd2d43b138,-0x442f5ce6025b0e86f24912d6be053fe26bd0,-0x19fd034fc95a9f0a128106b79d4ba3b39fa,-0x82e0e890959f116219134a124fa219000,-0x216d9417eeb018cd8a8ccaeee2f1ea78,-0x6c151930634395047d77bc1cdcccc8,-0x10a24445ca57b03650e7cda1171af,-0x1d515bf90f7134f808eb51e5900,-0x20f4f6d5db491d102e5cd1bdc,-0x11c350f5c6160c0faf8cec0]
def m22 : List ℤ := raw_ints% [0x0,-0xd17336a5f7e5cf00f57d38a176a72bae8dff2de29c8887fc4eaca9000,0x1965881bfe3efcd580507fdf47be424d71ac6c81c605aa9da84c84adc00,-0x17eb1d0834903efa72d66221cb6f918c79e822900177070c0b8824be9c00,0xe9199bed428bfbe09bce3af7110a03a3ffdb9509a5be76ac9a2278b67c00,-0x6737af908a2b48bb1967bf09fea2aa844afaa182e3434cd2b0abcc16fd600,0x23690b42a452d8c4604ca076469adbc489721409f890a1bea8e96c4585bec0,-0x9cb7781e9075d14e3f613c3258bcab66327bad5eaaf16c55311866bb80b400,0x23ea3b73f3e3c793bb2a965e9c98d9e56a4c497045ba72d5411a6ebb922d420,-0x6f4375695cc5fa7d9b0dd4570c00005639571133ac0a72afe31f3a9f62cee00,0x127851a17206177f1b10c98dd61e133409dcd8528958d8ae58bc55c4f8a91850,-0x2a88e52df45bfea58df307f28e99d41da6a842daf5290607baa5b3512a37cf80,0x55ae86c6470da9deb3473834cb2c79a12c11149694c3b05aee600b4b0d0d63e8,-0x9807aa5de8451a057b60e6bf15cde5680cc341f74155aa199c06ec87b5e00640,0xeeef5c5e327d4fb89f10606b1f0e81083d3f7c5f98c07018c049626a91a464d0,-0x14e16f1b8b05883b6e4a136e1de15b167c8b6092dfe36405a03babd4eb6f5c440,0x1a10faa0bb512df760286daacc5fc13b2f2a9b8bfbf99bb543f45c8ed8c10dc04,-0x1d2181a3cd11d00b527a6b9237aa2a0f7911c2a437b233faca3280736069f3520,0x1d347c48a1c8c936749f1a3de09cd468758fdddd486bcd5603f0b194879643d54,-0x1a4deab6cecf4d7f6a5bc9bf4d86a3b56fcf8a66049ea3fde2dd17d6e534f1e40,0x154debcf5adc4a1c87254e5212cf078f335018adf76488d1e8de21a4732cfda76,-0xf85d6cd9a595dbc6c0a5449bbfdea3e659525706d88e91e8251056f5fbaff850,0xa2cb2987468e0c7e4efa215a543be12f4f898a8d7ffb80f70c73bcc0d2140774,-0x5ff1993bd3727ea27c511c0382183ef4e1c616510366a3b679cafcb89a2694d0,0x32cb67b4b87b5e0f71cdd5d276b8a3a798be7094f6fe749004a15d81da5b9ae9,-0x181f69b6df1626ffb369d06bf0a298466943747f5effc2877262ae3399414888,0xa41cbb35a495a2f53d0f7569a452de254b14e599ce2942827874c3b54243b50,-0x3e53bb373df0c8c7914d81cc954ec8911f6c6c96250ae5db00f11532143a2d8,0x1514706381c90b8abe1b34e67ac3cf07b3a2492702a4ef30579b14e2ed14914,-0x653936180c2abfe87a87cbd0f0dd01140076e47c2103f8cf2797e55f44b048,0x1ad7cd3cb988e43555a2614b7be329a7b05e73c8b9a60e6e5b7559e268e5a0,-0x6421a7687183f9af9f8d4465236b3c2081d643f5ac475cb1441bb6e20add8,0x146719222dcab61163c1f405751bd0cc58fcb2a446fc612145e21b04b70a3,-0x39bac30017c0c16b04533be2c606a522de5f77b5b2b9bdcace4b96057f70,0x8c9c65a0e05edb6e959a046de36d35cdfbd35977a6a90e77c8f75248814,-0x123fa100cf770b6e670bcb8bb03e88138b0e76e3c41ed973310616291b0,0x1fefad49f41e7acf9776d4fca4745a90fa188709a7000dc4a7555ec256,-0x2e76f7bdbd3023d57d18c475b3c5427c5d5209bc1943f3fbe14954f60,0x3748e98c9f451733658df6f3e19340b1acc87d0e9b80c5e1bfc55574,-0x34bb30af416fe25ad93481644a3b4d9a370cd476405bef62ddafd00,0x27580f5465af3d98932d1703c513d82c55cdee2fda02fe5c5ab55f,-0x16465bdfb81dcd35c3d4df30e7f08d69f9103209a8512b1954d68,0x93533c4a4176e2ad8613bc91cd4c6e1132258eeb96f50906ef8,-0x2a4fa92797edab76479a7d393813881324f5586ca03614f938,0x7e7cbfeb5a0b5a5a6592f924b6513e0fe670b95d92db7b18,-0xe0d7f2871340c28df152227d9c86998bc224d270f36348,0xd0e882f6237bb550e8075791ce1e992c7fadd835dde8,-0x532d04a669bfed3614659b95e78b2019e169a69098,0xa0a0cb03b0a677ba2833dde5c7cf46319d7a611,-0x2b2d339a7e78477587840000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 26 80 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 80 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 58 indices rho q22 m22 22 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 58 indices rho q22 m22 22 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r23 : List ℤ := raw_ints% [0x5e4ddce17aeace243a63d0969665e66f7ca4b0bd5600000000,0x8b83881f3337f561281a9548604fff3bacb93f69b530000000,0x625709f6efb439b5b9d015a4500bf74f45d9d39c835e000000,0x2bf79282b494996172daec9a1749424c4f52d5df542d500000,0xe00b65da962c8bbe09668af4745b45ad050c02d3d51c00000,0x361d5f95c0c6cbc86123b902a4acc2ad7d0bd8ecee08cc000,0xa4dd8c74947093d4ee6644991a839543570b0488508f0000,0x19654bf7aa546b75f0c55862f3e441bbc69e20f77f606800,0x338e2fae0753e377cb9bdf168355dfe73f60a1e013d5800,0x5752a5b7b6e6fa1bd3775aa33da757aeefa3f84f5630c0,0x7c88e355a8ec0ec4c98595706b89957af1e2c9ce91d80,0x967d8dae4bed825af9f2e9f39a2072675e194187b830,0x9ab7742560c08ffa89f2260d3257fa9eb388a8a0fc0,0x879a1fa322bc8ad292abe29600dd1b6a2a2eb6a284,0x655761f74513f12ff512a405f486d5edae70b98d8,0x40796dbcd9a1dd2f4218f905abf7eda036f95101,0x22cb1525f9fc8b688851947daff130b3ed51480,0xfd5235b9936637cd82870c01bb158d6405108,0x605c146a0a6107f108c40e1e3362de59ed70,0x1e4346187a85f04c89098b1213bfae3e406,0x7b5ec455872089da91728640635cd1300,0x18dce7e2c5f266ed72f920041fec9bc8,0x3d09387bc9637795e14260fd477a78,0x6b35bd54bfa229dae112695df0d1,0x780cd5787ddfaa472f10247280,0x406b0b9da22ca0c7a23959e4]
def m23 : List ℤ := raw_ints% [0x0,0x1affda0b64f49faf1fa5244cd04b8ca1804de4ea362d9987862441c9000,-0x3401f73d1ad9f2ca460d659e9f28a4bfba739fcba86bafe52b1dd1a65c00,0x309f32478d2e6c06e7e715e8b04dd77c92fdda90f37cf06f305405c50c400,-0x1d64716d8d000dea041bd32fb36c4e6ba874f9307a26950d25f54ea1761200,0xce9f8469d7f53edc91350601cbd80bc0759d2df203b0851c8841a4708e8600,-0x465152dcc0840021697c5f95e1b91164d3cf80c69c9722a045202081bc5ce40,0x134a3433f19fc00fe76f8ff4cea9ffc5636d6eb67bf3e55b8474d4817c6ce000,-0x4620d6010902eb23e5f302281856a8380bc9e6243c13c04136485c60607a6ca0,0xd758038743edea281a65a531342886ea6de4d83e5d1de4d5ff1ee0d4ab982600,-0x236c2d41cba3b8ffb8ddc855fe965126ca41be1f40b7975205eb031b30d8a0930,0x50cee1307cdac74de94ba92f6244913ed757b42af1d5af90f938da5f74544a480,-0xa13225ab92c0def84fa5eca2b0a7ff8641b61ee902aeba58e7e0038f9c06b1d88,0x11b23327687fedcabd00f4747d138fb17ec14f5052a9d3c60ab881861e0a128c40,-0x1b857665a28b3dfeebf65cf3ba17c8e5f8a6c7b797de655d7c499741beaf5a7530,0x261094cb690e4b65c349bb90c83bd3dca2559a40ac7213e44c926d484e110a0b40,-0x2efbdd4c9f4c84bbf327d4c8c4daff8dec9781dd3a82350daff520010ae1ad5ca4,0x33e4ddee6240a00e8c0ad18c8bbbb487df3d83b28e49bda6344b9d08b046771d20,-0x3364c42a52b5b17c5e65176d4905db93e838f6a490f674cfb1eab81aab4a45760c,0x2db404eed45ada45e1540545d56b7a349eaf2d146b5ecf89ab3a55b55171ebcf80,-0x24870147aa186deddc893f4960bc9b8943c5d98e714ef8bf539a41869565df6b5e,0x1a3f7e603448431f21044ad06d4196ad605d1df3b9fc9bc9b5cf4d81c60df7bbd0,-0x10f4fa7b4bb7c209e7b936823fba3cbb55f7c97463ed5f0e837820bd60d97e4eac,0x9d7dd37903ea55f73e4e99889f7b3a928d5ee8c0c9529f273cceb55089218e990,-0x521046e7427d4b898de2c034cdbf421a15e2c07e4a93b065f2d50da6cb8cfa8f1,0x2653cd6e368efdf46b5ef7ed7fda3dbfd3313cb5cbf98b3e55abb00c94a4ffa88,-0x10036709c8bbdcef9db69458ef2d3aad7d8354073f1133cb19fc940fdd0eea3a8,0x5f85e1898109fbd4f038423fb35c6b4ff0aa7d1d83bc276519534de725373b18,-0x1faedf241426732491783347632927b6082f10dbbcd9d90ddbc8ad37d20bad9c,0x9508d2f08d82f672818f62d660658255c9dd97de8c44795ee87fedc0afe5dc8,-0x26aaf83017d279bfe77ad919b1a9fbbcc1b9ad65185c5fc21f24d8c454be1f8,0x8cef581454e53e9a591038084561824f0af70a043a7a8090f6c9878b6b3198,-0x1c044c1322344970592733f833fd4cbed62593d4b8137da417f38a53eec94b,0x4d36a0825fc5bbf918f6d812b6735a200b9250dcdf536d6d9c20faea53770,-0xb6d7de45ec1ab81253093f21751f331f0c4e02ceec1a09544d5d558d273c,0x1705dc67afb722521bd7cc95c85ac70c4dd0382c66eb9ca83b574fd81170,-0x27006fda36768e68113a3a4dade58b16bc3c0c0df69152dd688075c7c8e,0x36c8e76c377b87c266309cb9a00dd23a7b81d0b69c52590b3ca36fede0,-0x3ebf689bdb43bb2efcfade3de909d039a81700ab0cd027d759f80839c,0x396b5355686eb9c68700cf9f1a75f341e1a3ca2d5413d28ee4b6a740,-0x28f1f067b2f03487f055015099643cbd151fcc1639592663046fb77,0x160ed438211fe0b1cda52b7e3da57a982083a4f3caf63410d1c368,-0x8a1f337aa5c575cb8c81f4ae87e4e8e7988fab493f6be6f66be0,0x2556950239507829ff8e5c819c7af132b0e373adf6c6dda22f8,-0x685d3c102e2862209ef690f1544bbe34ed98e2389cb6629d0,0xac1fe2df5c530182bccd8435cf040312e74a081f1461dc8,-0x9311702d27e41c75fee18cce6040e99ddb614d2e39e50,0x354c03d7c06fab0551e8fddef9adbebef244f23aad8,-0x5c90137a2685e087041e9839d74df3ecbe8d3229,0x160b2c596d83dfe81c7600000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 26 82 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 82 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 58 indices rho q23 m23 23 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 58 indices rho q23 m23 23 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r24 : List ℤ := raw_ints% [-0x155ff8b0ee17dae1621ad858cc9a860686a5a6851be920000000,-0x1f9b7157b26e2947ae33ce82bc3932963a29ad15ba29a3000000,-0x16449682271a07618a0b2740190bb848ab87246e38c7a2d00000,-0x9f34ec4ef92eb053ec2d75890cb72593892fc1335cb2b580000,-0x32acd52fcda56be914bbddab0146b92c0833412f0251328c000,-0xc3b6fe1478e363ebcf3476dd79a8df65fc755b8a6df8999000,-0x253dc4ddada3795ee12cd50ba1a6cfc512ac050d283c09e400,-0x5bb8134ee775300c35efee3c4a98e7cadfe9535804d5bfb00,-0xba0d3e3cb3c751b855eaea8083f522f8837e8680e95b0a00,-0x13adcb4a0e3bae6c1d1cecc71d28c8f8c30ec85bac2a72c0,-0x1c0a0e24421537b0d0760ed738a3cf97c9a5af70a7093c0,-0x21d99041ce2c32491c24e3680e2deb6c106f5377cd6690,-0x22c366d813fa9935099b236eb65095d00abb0c9de01b0,-0x1e6ee22513005429272bf15680cdeeaa8285f6662ff4,-0x16b72341975ab4470b0d562e19208a4be532e87f8c0,-0xe6e92fe09f187adb7a6a60bd0b84d14b233beeac0,-0x7c6c702d7fa4fc498041a379579a88c80979c827,-0x38869cab4efc61a4237fc8d7ca418a4bacd8e4c,-0x1576855d10f2db3f5838cbe1e2a59dc1846894,-0x6ba333f63baaab86834cf8529128190cdd30,-0x1b5d6fab58723a9ad7b6dcea4771558230a,-0x580649db681836d4fbcace9505bcebe8c,-0xd78249ab7ce7dbaf1dae5f1b8308774,-0x17966609b82c056b85ab7ec03581c0,-0x1a52a7cd50cbeca5315a0cd1c897,-0xe1209b6b4c7407875b143b534]
def m24 : List ℤ := raw_ints% [0x0,-0x37afb1b78038895931449ade6d9bd20d18a0a8230fbe0ca784aac7ae9000,0x6a852af4c45197650b4a5d5b5ea44bcb708e79940b5e1ac8a8ed80671dc00,-0x62df65531ab0e74e287bfc736f4a40e2f0d0c82658191c939f3b0c3e7f9c00,0x3b54204db9f5235ee19db118fb63b1e81954e893189796c5ec6bbb4fc4afc00,-0x19de629a3ffec6b7ce35c158bbe42ddc4ee2edea89ea30adcfc772a6eee2a600,0x8bc0c389e521629ae528333bf69bd7c660d6dcd6fd8a8ae63454c17d39937ac0,-0x2607039e88c9df9e854685febdad35b2c4f066bc88720b5143c790933ffce0400,0x8917d6724812ec9ec95ad23d8384240f4a6a63054ec58ae4a7522ea67eeaf4f20,-0x1a1567497547c01ed78f012c74a5716d5e59af727f18b4bbcd1fe619aef8c9b600,0x4409389105ea01cfb4c00e8b77ccf685c2c01adfa3a32e40829e951cc15c558e50,-0x99c5fb3e5a03831fc55b2c9109ef97b5ff8dd720f5228752bac85385950857f780,0x12fcf83045ca780f8e8c5886ac6a898e732433851424f2be547a00fea45bfce69a8,-0x21057e57121a1db1ce36609e69c1fe2f9e7f45290fe00b72cf622ee1bfea70cf840,0x32d3c23e78a0c7858684fd834e9b7e866224826a676b74f2558bdebafc3d6cd2750,-0x458c4c923f9c3d9068171ae74aa69eb38904a025bfed3a3ebeab50c6c8be9b5e640,0x54e41ce826500bc6e33a587636c01ac1e0faa04bbb61fb4727a2388455a4a18ff44,-0x5cae1ffd99e00b0ee7636148ae80d969ced2549f835f37da8f3f10f3d07d9697120,0x5aaeddc3a3881974bb92b4f292f79bf00b01222a55606d5c165377a5356a18aa154,-0x4fa1cd17919cc1add810860a77a50f5edcfd2af989df7e1ebc2c337b61773825240,0x3ecff1702e09b4ee131833d173d9520386850e651cbbe47b4ec2a937aceb0cef166,-0x2c85036e3cb6c6317f9dc986a623c5241382d0ceed261d5dc9eda85365fb85c4ad0,0x1c599f1815db48df43d063cff47d79bcfed5bb56819a5a139cc90bba06dede38194,-0x1035e831ce351c7c82dd193a77f49ada51b21e389831ce3398d78937f4232ee6350,0x85074d236e4e3956c822698ad872610f32cdcef0b2ef946539173b054ac0a3ca79,-0x3d1b4964d3ee4217948f6db3be8ebdecd223cd8eecc68ff3bb188aca79681d3f88,0x19168a0ea999d48fe742c58c48c7f7ddc7a437c6840099f0082ba2cb20dd903990,-0x92ec4810496dbb851582077f78a6130c8c1c3e863eb7b7158faf238f0c3b745d8,0x2fcac7931903c92f0b276f1c39e23ebcbd8cc8038a41e3b43d90653bc87e43e84,-0xdc3a1fb511e35dfc67b65014d273b49fc5406f87356d28c784cf7c93c3cc6fc8,0x37e7a59db2e2a85bf6605e070b72ab487e0b5ce4cd311c72ee00af65dbce5780,-0xc715e0a2ad7c5de123eb66267ae4b0861fe239c2c3aa0a10d55ebc157dde558,0x269c3d64a869ac30573d19a180c0dc71f3bf2ef30b171e03b5601cfe1d5eb33,-0x67a2f17c180a3323664fba4f2adf190dd88147000f29aad78e83425f6c6570,0xee92d6f1624f7b26cc0da233481548e5e46063091b3a4a595715a7b6d3794,-0x1d2459c4c1b2271bf888cf86c778e1a1d58811e81e6c4ed26b19a53b247b0,0x2fc7847a49bbd406af04cf4fd6c4aeefcf852f4210a3c6221a7f062656a6,-0x40c8a735e6173b6e5cb98e36dc92d22400d554b4edf8c149c7218de10e0,0x4768cff7ab89a1fee9d5aafbbc98b92fd6af70735ff2979ff8f1208754,-0x3eacb4d39cc3a7dcf101ed9e5345078b36452d4af80d1596584f0ea80,0x2ab34c0be211435fe41b0b748197e8cd35e841e1ad2b363c2c6fae8f,-0x15e18e0daa4e12491d315d8732d470fd6b6f6bb58259d22e605fc68,0x81ab64d77542e5fc46e823be588715f56e575cf7badeeba231338,-0x20fb4e0f909d6bdb3aa6b053dab44067304fcd12d3cdd2d51438,0x5629433950d7986fd19bfccf35cc448be5203cc4d97722bca8,-0x83cc87a23aa9d2c6c4217d61806f0e318722083c6bd83dc8,0x6787e13bc3b68977e4c021a8dd46d101caadc7bcd01588,-0x2224f5dec4e703f108813b5cec22063d4bc851665b18,0x355362dc3934495accd4476fa940cae63b442fc81,-0xb407adb52a87949e039000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 26 84 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 84 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 58 indices rho q24 m24 24 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 58 indices rho q24 m24 24 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0xe1209b6b4c7407875b143b534,0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r25 : List ℤ := raw_ints% [0x4ab358cb5d491cc77c4ee9844b1e6b99185f6b31f3e8ba0000000,0x6e6966e86ed5ac48821eb28e818d754aed2a16eb6b0645f000000,0x4dc02aac26d4b9eacdd9a144c4aae9bf8a6e4cca2107b36100000,0x22b9acc932afd02976ece9be6495778e7993381b9639ee2680000,0xb0c0663611804945694c2bb10f1116b703deb64d220989d7c000,0x2aa3dfcb7b23ce7a86786f265ded9fdd76b4f0eeca9eee461000,0x81bce9f43b00e358a54f77831d4ed601dab950397da03df6400,0x13f4eac54317fa22d6da4737c9518934d0ed80a6441f112d300,0x2873e5b330323ee6755ca808b6112fddfc3fa428819b1f1f00,0x4467f681bc8f9764071f6db7e49c90aaafbcedb9517229fc0,0x6162bb6b2a22401953b43e4f8b74354704c2b55b2ea15bc0,0x7575bf0cef8830721bf03c9eb9cf81c24e7d2369de44790,0x7882ce202b508fc66329018794fb4a869d9da3f32b8cd0,0x69633ff87e304d07d5cb07cd0b6d566c935b6810d3b94,0x4e9225e0131f55b62aaa08d14d45a3f7171b68ab6620,0x31db3f5384acd3d8638ada0aa9af0954e127bc1ebb8,0x1ad3f02edca192d62d2b5ec0ec380a739d6efdd488,0xc2b7818dc2604452e9bc2ae995e61e10af607f15,0x49d05fcdf17579119e2e8bff23a850ecfd9a600,0x17184a610116d8334a19192b0751f2b3ef328c,0x5dc24d19a994c4c39edaa14de1a10d44dd20,0x12cf053c3ad18a3707f62c751e6521281f2,0x2df02d4abea73181e271e06246711bbe0,0x503b563d3a144a0bddfc2a0d3537e24,0x5944a0cfd6c8a5eadfba723e67ac8,0x2f8e66c1596ec959bb005267cad]
def m25 : List ℤ := raw_ints% [0x0,0x72da5e8a78749b47f59d7f6ac211613b02cb5ac85077fa1981a03bd809000,-0xda34e2a64ec86d881ce6d814dff3cc539825dac15772173ddc69d8d4ad5c00,0xc91fb5d1dd9e6143bcc82f2c58ad6692f3deb43023642d822acc6deb927c400,-0x77d0707c9561bbb3d0bf821edbddadfda9f10bccf2c8e597a59ff20ddbed1200,0x33da6ad37cb94a69201c464e91ab51e6bda2df489991a05932256a3e078ce1600,-0x115fafa0e6df8b85cf62a08e8e3ca5623fb55c05e84c21e57d6015ec654f517a40,0x4b0a2bdf00b4688edc32d55468b71ac6e1596ca79b571dc9be09f689a609e7b000,-0x10c4f262bf323efda837853a2c2432847384d4ee8951e535a2e2eae9c65a6eaaba0,0x329dc2a1919e56cf039040b6dfd189051020486c40f485a382d29c8f3480143ce00,-0x82de3f4ee98647478488bafe9a0aced66ba7a2124dbf627a4903bc95d4cd6b6f330,0x12518e7fc558e8092702904d4aef3d6a6ccd2f6d247c912185fa209e7c6d2acacc80,-0x23d9e9e3d6c5fb476c3ecd73c5e9e188d6602243b4b4afa448bc56374b6b51c94848,0x3dbcf8b49be5345eccbc2a4dd000aa49fbf02f5db8f3b7acc6f72de6cf9afac4b640,-0x5e108d98e514f62aaa00f5b7f8f4cc1a4c6c709d74124d96ab100c227e1600c3feb0,0x7f5ac553487487e85f25f4ab46d8d94d1b5df3a906a3e38b27eade6f4c82af28fd40,-0x99bf266bbe1f188e7cfec4c20677b8c85466a019acdd44614e7af646c967b1972fe4,0xa5f0477d7f88f36fb778caf2d83834702ef616cfcda8459be402d6dca65211542920,-0xa06ec2589df64a929a0b0843b3b7d162d4f5c1e00c5ed7410679e128ee85a42bae0c,0x8b226de26fce8e7c5821d91c2629c88f276e6082bf14c2cfbcc814cd775cd1573380,-0x6c534b2aad13a9792de8fa80e44f92338aad526c835555a93f714948cc2e0f1bd28e,0x4bbd0280b46ce5e8b483db288402b78a01f05fb9d10f10cf5dba1e25f22ebaf28450,-0x2f8be649b40522848df650d62aa94370f9099fd500d87092be9aee1269f7e86edd8c,0x1ac877f7c888b9b93b4c4f8b75d090601e321b557fa53f703dd5fadd7615b635dc10,-0xd85c71f52db4cb9c6c7302bacdb4cb13f697240e7a9962b63ec63ce13ca5451f681,0x61c1728237265d9410a7aa665bdcde81065e7a7b9df7339e335dff27eecafbaa588,-0x277119faf6276997389d9d739588d54163e4792537bfebea6155f7abf94d942b068,0xe2c6d56235318327e9588a2aa195e0a15de669b7e8af6d1d8cb851728fffc66e18,-0x48592616c646cc870d045057e34fa7b8f59b62cc36de41f4e7d1502a07ba3edccc,0x14697bccbe2ae864488787e3ddd0ae0020b66a3437ff4e54d6323ab54b0e8f4f48,-0x511d751038a58963f5e6ba58f29fa630161d2dcffafd93e78a7bdba5fb04da218,0x11a3af3a57922119e78e4c16d2957992a5689854fa6c67b6af469d9a94c984d18,-0x35657aa2706a1985ff082495fadc3a4d302c37145d591223a56d4ec07202165b,0x8b94ab3947dc06750478a0942ab499f8a83adde8f70db42e9b98c147d4d6570,-0x13854ab0aee85d83a00bdc60400dcd6e61d830bb42a4f395947f0877e8699bc,0x25017c96f8a6c7e6a1be7ac94e1aea20158c672bf63e543c4074ff3b8db770,-0x3ab5e360640be667423bd100913d13c2ac875411d675f88ad6ff06fc5309e,0x4cd3389ef1aa1d465b16db4b19421746dc650e89165e5ba48d3037a04960,-0x517a453aea7852da3899722509fcbe3340fb85f10bf25e00db6d59fe6bc,0x4491bb02c2490862cdb2cb3db1b5018fd86a82540f5160fd9433d180c0,-0x2c9eaa8ce79d068953b275df3327678c83859d997579484ada21865a7,0x15bdcae7e1deacbb79c0086c9b38e1cc9b443e8ee36f1d6dbbcf8668,-0x79e3be605f100419381119711d8c5138cfc2297274be4296aaeea0,0x1d28d7e867798bbe9339ed1a8a94572c40c32058d0cd8abaf8df8,-0x472bc178d31f92ed9cd424a7e6ef606e50c688f5b008c38e4a0,0x64f1191589b51d9c60faf6a4b745185295801b1ec089afe48,-0x48e0ea04bcc69ee129ff0eca86fcadf8fe6414352ea92b0,0x15deafecf4af4c8a3ee8269661a9e4a900dd1fb423158,-0x1eb6904dc2bb4ac22c1a83355b9e2bc8ffba21eb19,0x5bdfd7939a8d6ef6bed8000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 26 86 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 86 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 58 indices rho q25 m25 25 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 58 indices rho q25 m25 25 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x2f8e66c1596ec959bb005267cad,-0xe1209b6b4c7407875b143b534,0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r26 : List ℤ := raw_ints% [-0xfc7a53dcd9426ead19aac70d5d443efd50bcccba039b8de8000000,-0x17505efd3d41f1bda8e58dc7fba5c08b20817d123a66e1487c00000,-0x106900ded0f9fb5cd87868cc5fd09c01f9981208fa3a981c2c40000,-0x753617232846b37bf58676efe86c1628ee83ba721e8659177e0000,-0x2544d5ab5d5577b8686ba694db887659af0efa7bc96172c395f000,-0x8fc68e4517d353a64cda15edd83d393ba8ba612d0d87ad4717400,-0x1b5331e957cff62fb2f6233cebd1d369976442001a0b7b3798d00,-0x433591f98383b05524b6caafcbf19eebc65c32ffb2a081d0d1c0,-0x882495621176d4b157e2231aa8ce21f7e080dea6f1fba6fa380,-0xe60d7217653b508319134ef318bc566839c17129249d69ad70,-0x147419ae177a6d859f030da71c4fbc01642631e38e5bfaffe0,-0x18a61cd731d279050128a6ceef521d17e5b43673896790494,-0x194423d1af3b480c1d58b4c10b49856eef62845a6bcad248,-0x1612e3014facad8ad24383dfdcfb914f4be08399f210561,-0x10707fbf90970891ecc5450cbfcc9329faed8a92e00a51,-0xa6b64853e5d67bc7a00ac4a781f192dbc31c3a91553e,-0x59989decb0b513a0f5e2e7f52e83c834bb4e63913da,-0x28967c1e0b9515596de12a3faba1ee2f9bd3eb7667,-0xf5d065baa8e8d65bfbc34ec1ad0849964e09529e,-0x4cc91b5948f651c9dc8d0b3c510bfb0e3670fc8,-0x1372cbf24f0e27f5e7d2c70b8dff13a8342d88,-0x3e4d3ea0cc17346661f4a6beb9001235473f,-0x97d654a0feaea10d64c64229ccfed3d849,-0x1088d77a6b5340f4cc0f5c6869eb4a6c6,-0x12590f0f4d7876619cc0aec465976be,-0x9bedb20b86b034cf29d3953b1969]
def m26 : List ℤ := raw_ints% [0x0,-0xece262fd987080446a94d6cc3043d889b5c36b3d25f773d49b5a7b6d929000,0x1bf118791f63dac7826d70cbbe768b56c69ce132ec45b4fef969a4f36a58dc00,-0x19940b6431edf24330672a2b70112c744ef2880ef53845cd6c1e4c1c08a009c00,0xf215190e23cfc9c57647534a011de49e00c2793963e1ec18b829d17eecb9f7c00,-0x680179b58af968bce7186177c407c8b36ef2a861595a2a7a85472516a1b087f600,0x2295f7e9abad26cb42482f0edd40ff775e234bb48f41d7639faaf0c34d7cb1496c0,-0x943847e2dbd02f630783f95fbe6ce0f1e5078b02f4682b50b2ccc2c9e3481efd400,0x20db569889a5961ac1a41d1075c53c52137e26188ac6227e73bf246d8e1b160f6220,-0x6259650dae7d645bb43795d734a7737e8acde41b221bd08556d968c36b4d443b3e00,0xfc1711bb05a3c5d5bdb85acc1be59768fbde686d6eedf6afd4cd4149473a44311450,-0x22f8c1a5f56da7848e53882cd90083d3735a542547cb869e859b87b50c7b7c5dedf80,0x43cf0daaf845a21a9b67f01bbeac5fa19c5122e5e3aaeb271355d0fa218e80a546568,-0x73a5e06914c2b87f85f5e3153fba702649625d5d0f38472c38c95941d36385dd8ba40,0xae70dc351e5b6998ba8a4d05a9d0cc26b637d3a01c2ae77b29a89c07e3850fd5215d0,-0xe9b8b40f99eef2482629264c60a8273b0a6801dc735c0add9b21ac9865ac8b9ae1840,0x1171a8ea22ff44ce73e9a179459a9980a1b990bb36d1976afa57963331c39306744284,-0x129d7353441847bc4ee59b21ac3b46a935217edb54e7df92c2c6fee092542b20989d20,0x11c929a6bce16329c43348712645f5a422f6b1536ed71dd49f9a30c5ca065ef61a7554,-0xf3c3d0bd3e841447b47ed8d5003dc7e5fbb1eac7c63309147658c81e8744428635640,0xbb5a153174f6e82aa770868301a2cf6aadf8e4b9ae7efaccee1b15218d01d8393b7d6,-0x813b9216baaf15ab4d02bc56bd72ae0d19188cdb790e3b957d89dfd5e5a2d00cac150,0x4ffcc0bfbfc2e8181308f6682533908458e7fafd0dcfa71444a2df7fe3ed322c002b4,-0x2c64557fcf28fa90976f097b8b1639162d2109617b06ec54c243bab6becd4b6de65d0,0x1610c36c7fe68ad9e1dcff5fa8c8e69358ecd35e6c5e7c6fa7a582a0279a866c88e09,-0x9ce8cf5ae2131225a2529550d5813466cd494172fe82c29002cec3ff2d23a36e2288,0x3e383fa4d39406120be2199b03e997e5e86ce63cb05e9c73592357f0b23667a4fbd0,-0x15f3ec7c5d6e0fe5aac38ab0415db9bd12ef0c25dcbad8d3a5a3ded157ad7eb9acd8,0x6de7b9d0d10648e7ecf21299330d0a6cfef367c7322ff4228f44b9a3bc7be3e9e74,-0x1e6092928143193e20253a94a3505d4eb43aa025f60b7a6ecdafe4367145d3ec748,0x761b924d092fc115d0254d4b81428659e2fa8e68fa03f34279e086c2512e297060,-0x1917f2129082c015f263251ef79aed5b534081e2ee4a88895053ec31939266ecd8,0x4a1967b4690ecc428aee1b0073078dc72a8751448459da5c752b2fb3b5cd0cec3,-0xbc9febb6fd6e22cad83f1e971b57acb3c293f40ec351e9676bc7dba0742c5370,0x19a398844e7814fd1417ca634ecc03ccdda1fcd91a0bcdcff1a2030823d56714,-0x2f23759d8b7fd136453e2d7729c823022eda5c6a4778e9a12cc1ab6011755b0,0x485b0a9c7d58c7f845c00fbbfaf8bf572a50844e5151b380d9cc3367a11776,-0x5b5accce68905d66432907c21f1fbfb4613487f9b644465b77d4a6795e660,0x5d32aaf0a7ad68e96e3df51dd35435f7dc3eda2d9dea9c800e00a4c91e34,-0x4b2f4fb564e6b101b96801a3e65ccec868e3352b47f246bedca249cec00,0x2eb6d86b853dd8e93b07bb9181a2d88ea2016cacbbd40f85e728b421bf,-0x15a2e130b49c62620d4d5074a27167c70f8ae76b559cd6fe7812cc768,0x72b6a62d6477faa45dcf386b61aa3dffba96c793a1aad3faf111378,-0x19cd3cf8929dc9337e4f7c0687fc8d1559068fb94ca1510947c338,0x3ad118ec11cd862376a942cd025c9ac148bc2b56f54a3e59f1b8,-0x4d5281112240c8fae026a47c64a477ac90de4392b4a1123848,0x334c55533178eceaaf49df00f25eb9081ba5337c43928e28,-0xe01450a4d404762ef600da8e0a45f6692cfac42643d98,0x11af500607b59296cf6da5a0c854390477f2611f3f1,-0x2ee059c862f636cbd4840000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 26 88 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 88 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 58 indices rho q26 m26 26 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 58 indices rho q26 m26 26 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [-0x9bedb20b86b034cf29d3953b1969,0x2f8e66c1596ec959bb005267cad,-0xe1209b6b4c7407875b143b534,0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r27 : List ℤ := raw_ints% [0x33bd475101daeba06486ec94f52c75655ff1b3f09bb1aee9c8000000,0x4c69adb4c6086ebfc1b1173333d31282b53b34551ea3fb9e54c00000,0x35c356f75c0215286adfa897aad6fd0f6e37dc7408a2e0add3b40000,0x17fd683fcf3d43dc745291dfa099ff0e2062edde77b149eb79320000,0x79fd0c0c6f906b13e46aca7d215cff78d75d46970eaa69953753000,0x1d65de6d880b3a60db697f2597c86f4fa8c26f1233af38543843400,0x59588a49b984e89c1b5c8d863f600a2ae9857622b4ef2d05bc2500,0xdba10283a0b2ca16db53976855292340261a738ec0315629f25c0,0x1bc9d140f5262d367c7de0032803bd19a1d3abc07932fa51582c0,0x2eecbb00fd941c7e9daf9a9a1385c37d7155a9c505d224991c30,0x42b41056b5c0e3c90c9aab6d55c3481866940a11deac39f41b0,0x505299c74eb760ab714f1da2c9123bbe2dd0d5410899b28ae4,0x5243d9e650c1a28d6305c8e3b48fb494be6f8b5e1807cce64,0x47ce4178bec0d229f73f312529695b777edf1aae0839bb55,0x356ccae08467b4967a3338b0c58706745b8cc9d710adae0,0x21d35385e6f4a76e962386474ed40c9ac126c6ed9c6f35,0x12287380b658f21fa0dc4aca0ffbd1f7b76ea52da5d6c,0x8372ae4a82962d7c15d5ee830539703163158d29d29,0x31b045c07d67b628a233cb9e5b863d3cc82d1d5710,0xf7f99b11004fb83e78f6e008336b39cf020c398a,0x3eb4d4714f3d69fb046c50cd15cb6bbb128afbc,0xc885430ea97540001c2338b87a67807998c2b,0x1e7be81106b0aabb13d510301a542f0b5e20,0x34ffee6722208984cf363e306abc1120e5,0x3aac2ecd634c2f0b35340aeed5259af4,0x1f14f2bd27e577d9860a996db270df]
def m27 : List ℤ := raw_ints% [0x0,0x1e892ec2b0a68088d1bd2fb05238bee9c06e30d2e1e4e5ee6806a9e91fe49000,-0x3941d0fd2f35fc8d6a6916865404bb62f9a39079074fc54de269e4360b5745c00,0x341064b4056fdc10938994e079e1bfcb6801b11b0f0a4217fde8c1bc1c9a3ec400,-0x1e95b44f2d7cd7afcc36b3d1391e0066d6a99c2a3345e92389af8a1f3690f841200,0xd0bea8aa70e02596656a7168ff37a01557e5c745967da6682d96f95ec572f462600,-0x44e7872b7fdb3f198253b7ffd62675a96c9286a5ffe21f03a2bf42b0efe10f170640,0x1250bade9e0882b395762bfeb1751e00c7ad252c0a3fbac120e0a8a1af192decf0000,-0x4072f801feffc93890cb4580ae31b002ac396e350666fe3e15709b4d527e3ff6ca2a0,0xbf56942252119da99d092826df256baea90383f769c4a0cdb4f439005b7d3c2433600,-0x1e64a2619fa2c0d34efd03e2bdcc7ec05a3aedad43cd0c047b742950935e8f1f0e0d30,0x42de81118944bfae77bf415cdae319ed9b0348348b4931dc439e610f1f29a328dbb480,-0x80798f512d158d616c757614361217fb6bba720d1ee0e76994955a1cc56af7a4af1108,0xd909e3fdac430017f1eb43fbc71af3ee12ce4fcf5dbb47da53673fa5805cc022077040,-0x14426e5d73bf90dd2f83c5c2d7841612ebe354815a71ef48a795d50777fc0c8244adc30,0x1addb605a7d8da9574f07f2823870ebba67f6671380d3b0db9b8f1d52a6d493fef0ff40,-0x1fbd7455de8a4e09e8a5b33676fc3ab1a35428885f196e030a762e69f9c449acf1a7324,0x217e5cc594b327a28073df31b5be983470773f8048a43ec2e600b18d99aee9b0eafa520,-0x1fa125a5942999ee4c1ebd76ff881ed60595d101c66e5551f8301773e6f9e0bcfa2060c,0x1ac3bd1f047f9ee833a4782913f57c4f934a0b5d044032d33127d9a9cb2bad5a94e6780,-0x144f236f76e682faf306daf1301d5f22552e630c6663a49aa911553504de942a0a45b3e,0xdd2896d001f438deb60da2dc0b1fc72a28b80012fe771046e868639bc2c8198a7d20d0,-0x86f8defdca544079f895c48072046f5b22742bb375924ed9ee99050cdfcd95bd84c56c,0x49cf1f040d7970ecf6d925abad8854e7c2664a712571249b4cfc38ad02e6342f424290,-0x241f230c8aad6dcdaa92f0bfe34c10538c54ce6556a35db9e12eadcc2a3319197e8c11,0xfcb0b24fc02d53490027364cf5f5152e967b738668be132fe40af3d3fe07a2f599c88,-0x627b80981a01bc600f6ed192a14f4a7899cf8504e68e424a00617d26da740acf7cd28,0x221e3113c695481a555f652f7ceea95291ff67d5f3554c4de38aae84880060722e518,-0xa788aa2d6d134c94a977bb50b8b3a33a4801159c2f9af9c63d597e13bb846bd42c7c,0x2d5d28665f977747c04f7871835de133ef89e6e54a11ed81ce6821ab1352c460a8c8,-0xac90a5143eaa43268a90516572a645d983019a012282f731f7d06b56d586446df38,0x23d1ed4351670697a7e9c43759ce1047e1b1c208b62df0122a6f3754629705ff898,-0x672d0b41b7d203d7c254d03362b4c16f7feaefc8d748ab612739cc5b5838d02c6b,0xffbda91e1d1a35fd23a5283c38506aee3c0478727ce26426d77ca416dc9915b70,-0x21c84a2b840e73255acb7ef7cdf8dd98c51218b9e146be376d35f2e28ade7843c,0x3c3a7f52932dbd69e251afb6eed9b267f028b9689e49ae95df4aca7723f5b570,-0x596d8dd2bb87a687aa3318f039517afc680baeaafa3eb68839c87b13b9d2f2e,0x6cebc88099fbb339fa1fed5926e25b331286ef3ad24da11ed58a4a628308e0,-0x6adc7a6dd85f156c4c60059b52e9cafa13b6b1d6fdb245bcd6eae8f8a2cdc,0x529d3a075a2d6374ccc9b04aee4bcc44a29d38a54189c37391e4b6d32e40,-0x30feea4c9047a5f3bc3b713aecb03b00bce8d648e69e1b14d33ba3cadd7,0x1590399185b57b3bc0f06c4abb185bc937068dcb6439402363e25ac568,-0x6c14a3856d0b63432f83bc377467be6b97b6d9143e56e4f0695ff960,0x16d9153201b0c40ee5daa61913f26af1fbf519fd3a1eef498520cf8,-0x30a0c38013bea59c45f3d49429930adf3e3806fc6467e1c6264f0,0x3b3cdfb78d8f853f3a486b1dd599a611a2cec0b9ea039746ec8,-0x241ae9bbe867fc12a07c1796b2c42f37e79f65d2c14333a10,0x8f76f321c491d6ed75a2667370fdccd78ae35791370fd8,-0xa2e32c5bd4942f3f28fc8f2a3a694c45997a8739d09,0x17e99ab485d8318c701600000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 26 90 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 90 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 58 indices rho q27 m27 27 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 58 indices rho q27 m27 27 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [0x1f14f2bd27e577d9860a996db270df,-0x9bedb20b86b034cf29d3953b1969,0x2f8e66c1596ec959bb005267cad,-0xe1209b6b4c7407875b143b534,0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r28 : List ℤ := raw_ints% [-0xa503b82cbdcee427e5a81efe74fe945be1059c30ef6a373dc78000000,-0xf39e4915576b6c21204a4824d6fae39babae97f5e27f9ed5d21400000,-0xab5716407f9527070dd1593b13602048fa9ababe43e7a8803d76c0000,-0x4c6c3d5c91cc441e113451e826bd7c5fa5d3fe2e253e30bd3ca060000,-0x1846fecc3ca08685787b6627f667924d76f5f74ff0daa98f6b3c45000,-0x5d909039ae59e166c056c42234c9446823c77b01c21f6f3f90bdcc00,-0x11c37453158a23ae17b13794c61e0ede04968e6e2ad55fa4cfc9fb00,-0x2ba464bbc7f2583b0d8043304b61057d6ab2be0cc7b7117577bfe40,-0x584bfbedd83754ab0aedef8a86b6166ab871c870ae8df8776ca9c0,-0x95022f5446b32d5c9968566c3ae26142e82b9f524115b146f8b10,-0xd3ac2138fc4877a25f4cd56d30ba8effa1c346d0e86f954b4db0,-0xfeb4cf32b45e4b3a640fd66633877c6b4e812caf1c7cdd265ac,-0x104a99108b3d56552d32e4583927aeffbd7f1ee7fc2f4ec01e4,-0xe3548d5f4bd8ccc0df6d8d87719dbd00c5c8fcf9e3b9ebbe7,-0xa8fc5158ff23f41d98113610d252915ff8b9361b6c230d72,-0x6ae319717854060cc56a2409af52637d4f5580e32de61ca,-0x3951664ef45cc0951ecb90f24ebfe445dffaca6682d971,-0x19e75028adccf33b9d3b9e052f5ca44f6d0c12a5e2ea9,-0x9c796bdfcdfd3524f11ae9ded940d37e8bb21ca6218,-0x30bd8560113baeabf6fded47c611dac1ceeb499608,-0xc4e995b53680601815f35bce7ed7b4301c6e1f12,-0x274ab60b0ebb21059a5a905fc2c9744f984e929,-0x5f67a75cf9d47274e4851b67f0ad77ef4b26e,-0xa58d08123eee06235bcf149573e13c1f422,-0xb6e140dac1506fd1ebeb67e938a1b8131,-0x60a6e9670c4937caee006828f5f6557]
def m28 : List ℤ := raw_ints% [0x0,-0x3efaf0718c57691a3096325ba99509c21ce344b2f1e81a3bb68dbe70d1c769000,0x7558dc10ee4f6b8786477a3943aa3a7c22e159f99f1486f0a2fa66af7763ffdc00,-0x6a021e83623d3805298068f40cb81819d88b96b8763d29701495f4cc6bf17419c00,0x3ddac0397d8752c0bbc01414b29fad620e67cdc6f0d04e31f3f250395fd42eb3fc00,-0x1a3392bd37d8ca9dbb890b07575ef65a96dd54655e286bc9d3fb4975328959613c600,0x8962402ee90c04885fee07b298ef0c24cb477b475215f4d20f584e0b8580c8dfc12c0,-0x243ec9c6849fca1f3bba23181a34ab7a859ffabf73079f288c4bbe74118f3d4fda2400,0x7e8e5c516578c4a5277d6748827f4be38656fe1b52c3a056e0b21a7bbd584044c1cd20,-0x174b66bc5c556c4b9226bf34d248b3b9429c0a956b498cdad380b996fbab5d231bf8600,0x3ab61cacdcb03a089cf6c033193a5fff093e0e553bd642774bee238a0b60ee1dcdf2a50,-0x800f00a711a0f515697e47c070cde73f22ebdf7b4ee88d5702afb564c5e0496c6828780,0xf3d4c276ffa0a9feca43a03ce85fc530528b662f5a5e8eeca1ccba9b73edaa9df190728,-0x19813072f26d7ef9082018f3fdfde61e83b45306381af679b027cd5161487ec8c1a9cc40,0x25b8d8214aa888f938264bb23da9e95909129575f5bf01a96d7abed5912eb3a5a846d050,-0x31846fadbaceec2d4ef41571eb72efbe681ed4f59213cf7b7d4c8d9f459c12052144da40,0x39e248a25e555024e5b88af774a7b4ae66252023c2438f4da4d4f18fb096d27dc27445c4,-0x3c68e021e63d9ebaa161e686ed28c7b0e8dd041726f7bcf66deea981736f4b67069d3920,0x38643d46fed89888400d16c57b077cd9cf33f8b99141ae782465ac8fa4909132b2ea3954,-0x2f24e6ed41d9b4a81463d3b1343a3127d7af95a3ce3145b6b6e5d4851f2db03f7163aa40,0x23529aacc202813697895f9c29ae69c5fafe35b2f37128036d1eac75f2113de54ad349c6,-0x17b9204f6659387306badb3000966955c74a4cb41fab99aed2c0832641cc11048ed07bd0,0xe4704813f6e9de9086d6f8296ce80c2db5d3392a20c696f378cbcf4c2036dcd805812d4,-0x7b19a6fb291f749a9f9d955547a5684f9502c8467ad27c18498aca9f867cb1fc9bbbc50,0x3b51ecbc42255ade5517f92a5b81f3fb5f213d1bb0e437da9aa8e4f36fc9fec27a7cd99,-0x198433b98544b8e48ee284cce0c8a0d59de19d17907163e9d4289ac8eca1854ae309188,0x9c6587e6f12b58298dd074444cd42a4d9c737c6f5497bfd6c975e253276b9378546210,-0x3533dc83f0f8579c7193bb1069007307093e896729ffbf6a33872e0392b1d4e972b7d8,0x1003f0591c2998fad68277ea783b44187b0f661a619e22cf91db0ecf40df30c978ece4,-0x43f98aecb6d0a9601cc94bebb3c2b2fb4ac830581128bcb1dc559534b622f7ccb36c8,0xfcfcc0ebe733126369ca6b375a39038ea6fcdb0e15cdf55b020c3cabada50e443840,-0x334db809ae20d8c83d7a0da0c24c78b54fdb12bf988754beab7183b28770414c0458,0x90232d5bec5e835da7f2f00ccc55f35d49a9b1c60a64490cef97c41df7039b35b53,-0x15bdb0c024f18dd19cb6e382a7a90be31a36b7155e18c951d026daba7ed26af0970,0x2ca68c3e4df2bce6b941d9535c3b2a8e6487d2197b0d3f80034a71acb4795f1694,-0x4d2e7f7f576b6e60482270b9d95605b650f5ccdb4498ee741f80c697dc9c8fbb0,0x6ed61fb63699f67a81b62b9f49533a270bdb122d7efd755c163dc44b2ce528c6,-0x82330124727949f863a62d7981fc2cdb0abb6ca8ba8b8f1c28d950a42f2efe0,0x7acffa376f445eee648c5cd029f980a655158bd655b7e10f2c96d80d2d3214,-0x5af68469158c7e49ec09b945e35d2549ac83f16fb3e0ff6caac4da3f2a180,0x337a41694295fba0094664d1c96ebb943329dde7409ef593c451fe5b16ef,-0x15854cadfe25b432965e1762b7a42154a85300d0109cd585e869856ce68,0x65f0150ea8dcbafa03008e8b41c4512e0be73a135d14a2d6b30b78fb8,-0x143f2138a36a6de7602955fc77ababd7111118b1716097feb19c6638,0x283835c814ae30f31b0d81220b95a64bb4499d052cb85216722648,-0x2d635117743d55f90606dc2591b6ce136a24052102c89dea12c8,0x1968cf80045e01eb3b7df733d9715763fccb4667092d24ffc8,-0x5bd504cc417f675f4457c2a8a8ebe69dcc569eeb326b818,0x5dbea7b38ff5ec6893ec79d011f7f970f586abbd7c61,-0xc321faaf1dd4f18a099000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 26 92 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 92 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 58 indices rho q28 m28 28 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 58 indices rho q28 m28 28 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [-0x60a6e9670c4937caee006828f5f6557,0x1f14f2bd27e577d9860a996db270df,-0x9bedb20b86b034cf29d3953b1969,0x2f8e66c1596ec959bb005267cad,-0xe1209b6b4c7407875b143b534,0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r29 : List ℤ := raw_ints% [0x20120fe593de66d4c93ddadf7e156c7c05eea32d8c6cdecd3ec38000000,0x2f54c1310ba2ed45ee374b8cbd426cceea6e6162641b8b73cd8db400000,0x2146c7e30f7fb77f3a593fb98ee226dfdcf79032845aee652c5da4c0000,0xed62628c58b736487df42362258b6fa365da93fe4206a09ef0851e0000,0x4b60f4794dca4c51ca12b666a43ece3e49cb2d5c435c2fa63d6e6ad000,0x1226136d7de1c3c7c3a6cd082e52750c7b59ac6afaff97ac3b6e7c8c00,0x371a5f5c93771b8c823267c83a4a33a336b12bc88361a4213dbb75b00,0x874f79cdfb34ac38cffeb246be24a7e09b3aa7a05ac18f53fff76240,0x1119c3d2786cf1d78c10923a4f5d94972248682b8f2fdd76f8150d40,0x1cd786fe7b41e1c04fdcbacf618d811a80666dc4c703b7b85bf5a90,0x28f1fe3f50d980c7f8d0ead4ead2bf0afe9baea1b6eab5da08ddd0,0x313c8531eee2668c17a0fe3140cc05c3321bf10b8a95651bafa8c,0x3259ec1894d194175a6ce6d9a7d72bf793ec53babd6b56f6815c,0x2be0e008d3cc8976133cb458d681664632a462b529310d5d63f,0x2096f1537851171fcc8a1c2c9b72e6d3b69d666d3713c78498,0x14985417b940d004093973c9b9496e385cac167c5a5373d88,0xb0884d89f3d9252e6a2963308e3f4e49c8da0ddb9dd4b0c,0x4fb22291b9489ab0365805d2f24a7a9cd6dcd609b007cc,0x1e0dd9246c6108cb40fb39323ac4b0196876d80bdad20,0x959997737c3e1c4a33086dd3b1b2a5606371cb6afc0,0x25b93810e6c5a7da409490ec5916339d589db60d74,0x7842d0d500cdb20cfe06c827cbf88846939e3d7b,0x1238a30bbfb4f7b35965c560d0f9e1c517288b8,0x1f901bc643107e6971aa7f90bd7e8b69256e4,0x22ccb5fc16efb7fdd1afcf54848a16575a4,0x125a4318cb440157959b70f40f7827cf2]
def m29 : List ℤ := raw_ints% [0x0,0x81e58fea317448c60435c7dd0dc364205b94bdb112eeb61b288458c8b0ab489000,-0xf0897ff06563f30f3a90e39e885008a007f0c992d81a5650502473c9e63e3fb5c00,0xd7e94213874225691bfb87ce9fdeb61b8d8f9826b7daa7a272b2b502f9796f95c400,-0x7d26e1549e1f610b2073b47ad739757464b110b0556f4a67d8c497c130c96ac3b1200,0x34a725367e6069e74ee405068cb4af5debf3f58e67e9fc4a65b6ce6ec292d37b5ab600,-0x112217e7010e72c984d792c0a5c1d96b8e1cc0e6ccea144fc069712bd2e95ca339d7240,0x47cb40b368125591799adcbbf2e569d2c7859899b5db61216477381072d48cc11b6d000,-0xf8c7ccbbdc1d1a9721e1ad64f19f90ded6150260ddcd43dae83e641e5226cd1bb6011a0,0x2d6e8775d14c5b51f871d510a60ee6b812d6d7f0b1fb6c10d20f4959fcd08eae41ec5e00,-0x71923933759088e03e41acc09954d985d3cd6bb39122da8a8951dbfab75e3f4e5955d730,0xf59d842e58e19848cc1112ee8b392016dc8df867fe5f033e37e37fce543c52e72c1d5c80,-0x1cf8a7ccb4c1fce294b74dd7825cc502a7f429247be98f03d0b88a8c57cc299c6b9c967c8,0x300a85d9b7f19add89707844f68a4eefc1a2fffc812fcae65a8364ed70c77572dc44f3a40,-0x465fe32fbecdfca37414ed0dece4bc507ae23f5326320c5bf5f1037607411214023426db0,0x5b7571fe20840ac427da260f9fed970991ab204356fa0cc642ed436cc86cd830ec38c9140,-0x69cc9cdebdd1edd00aab68318b933d2a0084a654ee79164f27c6f62793d4cc343aac84664,0x6d371c1aaf1adce7df094b850c76f4cd872befd8b935582bae1ef501a0394292ab4921120,-0x64caa596e2dbe4c2a8873187ef92a02f6d762ea99ed0a769d2efca4055c99841a5e397e0c,0x53428f2f9d5b105c761f8bad4fa3ff0d7e73dc9e51e4db736c8ddbd897478bc6d65deeb80,-0x3d9a98a3638544c2bc148639df00cfe7dbcdfb3ada87a1cbaf2653f621184e05249c8316e,0x28d50102406e62f7ac7c6b488b4dbb56a1b3d22eb0adec3ac0cc32196e199f5b9071a3150,-0x183c649e8127123dd43af2f68de5e50eb3d75fb7fbc1f3ba4a1445282d2d7cf7ebb573e4c,0xcdefaacec0e05f3b67ced7502164f2bf07c50efe03dc7e1e1dd78968217fbea1b1403d10,-0x61b90a90618b68f399636f0bec110f2c37dec44cad3e645413d085d0b5290be9dfa531a1,0x295bb7ec44ef0222b5f56d691c00530e10641a0a2c27420c6c795e84beb84684eedb7f88,-0xf92dff5038442bd02a8468fb17d705a70bc0ae02405ea424e5d82ea53ade702c53479e8,0x533cc25c3cbec7bd4c8f7fc7de4ed11fd5b88f30c8988c2d151c0ab246035b74a078018,-0x1893dd3f840d87d1a1b2ff3bfb7ef5a07fcb7affe9d1302b80fcc81050e3cd6483750ac,0x66324d02ce1d11766aa71cb7662f9fb44c7cd427c00c63731e3996ab3a8e4ad3696a48,-0x174204efa018fbe8f914274ce7848825ce8c68316bc4b57a56de39e0d2607209123158,0x49b8f572a2a1e62dd464cdac715a2610d4f951dc5ffe20c53791bf6414f0236747418,-0xca035800f551ba39b88935d72b1b773511827f2c8b88179abaead1040e5a89c18b7b,0x1daa3f422db38c270f16af21272665b6a92dff6b1da6336caa25cc5001c66552d970,-0x3b31bedcf7b05b33b9a407587baf1a14847c7548986bc065cb4e9eef489cfb626bc,0x633135954d2a9ac44f4ab74b665ebc276ae70d698b3a0b28f25da1b8d1f7594b70,-0x89bdd1290d5924ca1b73d599913dd8a3de9c6849d916e8dd5fba896ad4cb30c3e,0x9c058152b301d58d88ceca8fdab8461725fbbd56ee80b6c9e8a9f6c4ba4acc60,-0x8d75e35de764d6f1cfe04c5d90b59f6c9289fd0e08da72b0a7d5d9860473dfc,0x6459f135a74d16f2fc83830fa00c65696d0502e543215e8f377b7f6f604fc0,-0x362c9083a7c2134895082547f911c43b550aaf945292b1194739d6862bc07,0x1581a12e6308c58789396b67ec478318b775b253a9695478e21b7666a068,-0x603cf1f40116ee84c793d6e1da2dd97ff1678c83d02d7fb010b41a4c20,0x11f3f656a8fd202357764a25e89fbefa592f61b3687613f9722affff8,-0x2146c13fba64065973822c7ee08540b1aa6939d9f3faa7bff18c6c0,0x22c77291de6e1e99bd82ae387a287079cb53561405c0e7d6baf48,-0x11e158f7b3f01de7ad59a821732a1a4b757fbad4e4181407c70,0x3ac4ee3b10d4452aca39d2c0849ada202205be82ad44c658,-0x35f050574fdc44e54a6d5c22835857e647352a05db7f9,0x63806b212c8985517658000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 26 94 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 94 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 58 indices rho q29 m29 29 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 58 indices rho q29 m29 29 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [0x125a4318cb440157959b70f40f7827cf2,-0x60a6e9670c4937caee006828f5f6557,0x1f14f2bd27e577d9860a996db270df,-0x9bedb20b86b034cf29d3953b1969,0x2f8e66c1596ec959bb005267cad,-0xe1209b6b4c7407875b143b534,0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r30 : List ℤ := raw_ints% [-0x616f3d5a1306cef01bfecda533b72df136ad1aae0a27443bc47490000000,-0x8fc07cf180f3f103512a47fe68c6c585ec829b464a92b3f6288f99800000,-0x650803af2b811f1ed9ea542c789a9d2eea5f2c8deb1e059f705dce280000,-0x2d0766ffcd4c3140edbd26fb95d8cdf3556d622ffb0aeb6a8d5c4a600000,-0xe4af6fdd85cd150bda5cd7a56e5f2ddc914864e2e8713e0b1c78a1e6000,-0x370972a687866fcc890e20f82fc13859d552bc5957f6e35efc4b601f800,-0xa7071cbae3b97d633eea06341f5659030bf1d12bea2f7020f9449ec600,-0x199f4a224469f020fd25450f19e648b4dcf25b4ddb7c507274d6da2280,-0x33c8b3f830f6fad80ad34843d23cdd29a835ad8e207871d08894e56c0,-0x574a7853bae3f7b42a4e48f2a691207080c231a1b68aebe09c75d820,-0x7bd9740005e1656d69479709f81c11a66d9e56abb61dd45da7e07b0,-0x94d598c1bbf4b399e08f8fcfb2de5153f35bbbfaa10b9d8c23a438,-0x981a0a305eac5d56a78d0bc1dbc0f15bb85c007ab5941a37d6264,-0x8473d6972cd9544e0c67da65ab052245021dd44f8fb1bd5bae7e,-0x624c9e2f2e580f5ba2b7303b98997d2bb42ee67732f1e4ac763,-0x3e117c0db14fdea8aefa75be95521194e77c128cdbf6259d34,-0x2138b856cfbdd364befb781ff701da5b502f0f30c20b96f0c,-0xefbbbf40cba6f6b2a814f4cc64fbcd6ad098bd1e4cbf65a,-0x5a4f92e58d12b2376f186b9fc72f66e703cf3209528502,-0x1c1072df4545d6d1b648627cefe7444bc9a4d31ca3830,-0x7116a2d1d097509a5fef6e1a437b60c6fa2fd7493c8,-0x16809c0b9ae20b33b77d1eb4f35098feb7c696cb52,-0x3678a2dae775f1b306f7d8c5ce3b4f149ed10423,-0x5e347ac01ea70a978f3f9d9d4e68207a405564,-0x67af313a0394786c63aa9818c9a7ccc1a5d0,-0x36937b68844decd88ccd2d79fab148ae36]
def m30 : List ℤ := raw_ints% [0x0,-0x10be978d305ffd61868aeec37ec62fe82bce2c73d370c57980390f71dec6145a9000,0x1ed200bfac4de6fded405c487d2a6f1ca10609fbeddb65205a54b2ed06ae06366dc00,-0x1b7e32541d7847e3d362f57aa28be1662ede8914fbeec35f2e88796cf028bdf6429c00,0xfd5680cac67765c189cb0d90e2389226a51a80a19cef53a73c16b61288b0046d887c00,-0x69df46c1408d1fb1d6fbc4ce526e2bd59e958316a812cf536afc3f32dfebf0475da1600,0x223679d4e6d808749952e5879f5f3a953ac6b1ce7102b92459b019be5a7c363bb394eec0,-0x8e5652fc1a6378687e91125249d622f58ab61067e2cf078d93635b3d1994ec847ca0f400,0x1e9903a8bffac7b6b57d5974d38e7794d3db3f994bad34e117f0bc79f4e5cf7c2f10b5020,-0x58b6a63c26d7d048aea84070e40e20c24215f8afc49bdfc8348110cb9dd5441ac2c048e00,0xdbfd82d20c8fa386f54a6ad573464858d8bbbf243b1de7b5ed745a5c5f355f15fb2975050,-0x1d7cc2f3c276933d68ca70169f639e66542266d435c2a514355b6f9d533e0a34b18868ef80,0x372aea3e9d4e38aa5073633f810854b6e0e3038489d3828804fec73927afcdc09d90f77ee8,-0x5aa767189b59c219b737e326197a4320e6512773ce2578d60c8b2fffa0ad07f456173aae40,0x838bc70a2fc3a485ce52be6a3594887614ac98323c6a77829dee5e287947d9aa9ca461f6d0,-0xa946a984a742a7ea5155248cbffaadade6bb10ec2565d9b46e07893919804bdff7d884ac40,0xc1ce749861670171d572d789fb63c5353d79dea309e66dc0a505bff1d5b94266654c2da904,-0xc5ea330721dbc53b5d3aabd6ca8244ffcb0c47d71dc5d49cae93070ef2e9a4cabe7d4bc520,0xb498891a5700ed01801219690c10833ab75a50c1123e1f6594f5e9dc36ffa427a3de586d54,-0x936ccc8b9c197ef6824ebd2aca25060ff9dcd2ed2cd842e87e75fe2b8c6a4863b95040ce40,0x6bbb085fa86f31705c79b2b2d111509131db7211d676fea0a276e93c2b606aeb61da12a336,-0x467a5c63e5e245a921cd4316c2021cd4039e253479ad96532f6accbf8d119a75835f939a50,0x2942baf410693f4ce3c4af24429765d58970a0551b6b03cf2f9a436cff880f4f1e8fd5f9f4,-0x1598d4a2926ba71096107cdbd514e48778d799d0a4f61ba770f3c4408b4d83f629c22086d0,0xa17c2fdaa725af665e36d6c7f239e163d8c0cbffafdd5e0745d4f37bb81ab46a8f9f23129,-0x433f6497ca7eed8f0bf459326ae35e8c52064c9217fb5a62ef77b933ba312db8b51de2c88,0x18e48f44b44c1354ab62c600099ab3d1ddfce07a3865ea4710b81f5180b729fab60944c50,-0x82a7047ed79b4c47ef1eb497bb1b55a87347473a5dd46bb0bb1c8e8ad843411c74d946d8,0x25d75ce24b5954604356d35f20ef3d6dede5d8413d1264e925777af30d5ba1055311cdd4,-0x9a270fd34dacd8c89a53444c1d56272be78628f85c77a873fec66ca02a7c0dc00cd3e48,0x22529e7d5c92ab6f470e5bba8f55608f16d5a106b7e56cce38428a2cf076867d7bf7720,-0x6a47f2999f786f94b55b08bcf5b37a903c704696c7c4e2c684b681fad65e75283b6bd8,0x11c06ad96b92524adfd1313a2d80abe8f187c62369465baacd82efe84e2a28dfef50e3,-0x289a1aa7b76ea0c81db50287b5926a4fdc971d40e04df46942a067d5ae928ad3c4770,0x4eb52df4a7a3916fa4db0dc2581be4de25923dc9426e9af758a4daf7e22efdee4614,-0x7fd68443d940f5db99f321c8e0b50826503ea2616e807f762148aac2c9e457879b0,0xaba07ac60e7815fee45a40fafc594691b9239a6ad5197ec933c9bb7d4af2e8ce96,-0xbb6a36ae4bfe345ea61d48b482b86b53702da7bc264d90e912ffa0cb3b5644d60,0xa34a8becfb155f483826dcec476c8f8986656b0c79577f87654d03c076601af4,-0x6eea7fe4c47c5aa98dc44c32a18b373e655dd3b03de7cda21d8f1b06186ab00,0x3919e16379a6a32c54618664b3891da1b6d67785dbed7883adf1276f7c561f,-0x1584ca0d968dc00f484004024791431850b74917d6498ef9a9a4907323168,0x5af0943b4949fe89aba530413060fdf6ca4ae88b69b79d20a7ef839a7f8,-0xfedb83cf0edca7e9109a53fed45c5e389c453e747780f3c1654ad5d38,0x1b8a4246c5cb06be73a5236ac98f7136c16087347f82d20cf8a8c658,-0x1aa6c5bce8ee1bf5a72d9ef6d48758f41df01feeebbe4ec96e8d48,0xc94a331da93de1601461a40f90112f7c4d3755db1e558746268,-0x259a20b26f8486e73d0ed79bbff3dc5080d4b29d55e4c4a98,0x1f071bb97c0ea236c7767ad3a09c1031823bc0963f85d1,-0x32ba5a17781ef5eb8a840000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 26 96 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 96 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 58 indices rho q30 m30 30 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 58 indices rho q30 m30 30 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_30
def q31 : List ℤ := raw_ints% [-0x36937b68844decd88ccd2d79fab148ae36,0x125a4318cb440157959b70f40f7827cf2,-0x60a6e9670c4937caee006828f5f6557,0x1f14f2bd27e577d9860a996db270df,-0x9bedb20b86b034cf29d3953b1969,0x2f8e66c1596ec959bb005267cad,-0xe1209b6b4c7407875b143b534,0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r31 : List ℤ := raw_ints% [0x121bf17ab8423ca83269c3e209cf5666019672ee20193f18915a88b0000000,0x1ab5a9d9beaaea72e061960254308899670496b2f0e72ce31e63f9ac800000,0x12c413cbd00a3b43fd7f32912b746bc95bcf2d8fccaaf4ae544eac6e380000,0x85c678be1d7ef86bc7f1ae9116cb1c88e3f41de64cf42306969353c1c0000,0x2a725390e58a721d5be44055d0b46c093dcaddffc81f3e769c81f57872000,0xa36221f3631bce05a371bfec2fc4783701da1435e66e45f8397fc3b57800,0x1efa1fbed822df3b93d6b14e8fa9f11f5fcf66f121ce2d4f420555195e00,0x4bff1594e6c183f7bd5aed2bc035dab18ed6a8e5ae9534803bcecdcba80,0x9984fc1fde8d9f912999da17d9b84ef897bb56138d9a4c8a9ef52eb880,0x102a6a23eba324a76122f8e964ae4f3be58de9f4ad23b947aca34b3b60,0x16ec698475083913c03b99f8f342259626ccdf8bec76bb621f6f1faa0,0x1b88241df603f8864e67068eb14a513be2a1f60c081b520e5cf047e8,0x1c1e55e07e7d5fa2ac5d0b3d948f329f95395f90d4064e2cda30f98,0x187830d0e906dedc24a12b0520fbe703aed9e15c3762c6121fb80a,0x1225966cbaedea4431f6b9ac5014367404fd040151232da3a72c8,0xb730b140fc404ba8af3407ad680793166c9cb481fab632b5041,0x61f8165b68eb2905e91cbc830c617b74b638879c3b29174848,0x2c253e494d2e006e858c47976b70a3a97db3ad92bbcf14646,0x109d32ae873fd920bfef9d85b83e6dd3e905475db3bb0cb0,0x5284d761ce35d14b1c0bc65bcc95425ad41dbd7cc139ee,0x14c2498eead85efd39b73310d855af4477363b75823e8,0x420236d639024c204caa62c8085b34dbcf8574529aa,0x9f92a448bcd48a59f667b446087f63661dcc2cd28,0x11392279c240cb42e6458eba30a8d8fc3935a771,0x12ed18ae36aa25800c0eaac96d9b61b8af2678,0x9f1deb697e1c5b2797c97962d4b4f91109e]
def m31 : List ℤ := raw_ints% [0x0,0x2289189333c5fa99257e8c733578c2ceda593baee418974a9875afdadb7889fac9000,-0x3f31b00eb1d8b5bda6bc1c379d57c12b0c1c74979a948092ba4eb108ddc6ecd0425c00,0x380789fc0d4adbc60a01df2a3c24b2c5b9cf1743c42fe13e979c639e5274338a92cc400,-0x2010bbe1fe7a3b0e405517a6ad402f57d6c9ba98c8cea66fab3f9546ed65248122121200,0xd50275d0128c2a189663d81810bcfa4aeb2ed5962bfaaa1795cba20281a30a85848fc600,-0x445e929b87a8e05c64784c54878eb9dd40461ecec2059c3b62e18ef314f04cc5fe863be40,0x11a7254cd4fb6dad8b34512071dda8fc9429c8bd9e239ee25f7aff8535291936dae0532000,-0x3c464515fa507dc4b2ea3f65754d056311ace81489121af833bdeadcb4e4d1a3ecbdf2b8a0,0xad6f469fd6d796db3ecce93b4839bf9733114c87d32b2ff6b18298c38a7495948d42c54600,-0x1aab2499fa8b8d5a87f705bf24fc49628ad03b36565dc28d49a98d12af123c1d01f5670d130,0x38b9c5fc3276bbba8a098823d820bf583ee649629133a73620efae084952cad575c08a5c480,-0x6938dcdfd16fc1691cf0fbe18c97d084eef139afffeba919cee1d686eefc2a62da59490bc88,0xab5e16eff38dc54f5eac306e3ad725a4e3015d504d28e97d5253bdf9fcee0b64057b9d49440,-0xf65bfc6ce1794ab15ab13d45070e000d812a4b4eb017eb6817ac5ec56cd88adc01ee71b1330,0x139f21e9927872e6bc94c0292c831f67cfbd0202bb0cbf4f6514771b6cf7e158045ef88a3340,-0x163cbd1dd8bae53074e6d54919ffb764147c31ac49e8487116049b5b046ddec99f867990c9a4,0x1677b6f2d826cc0a1a1c8ec605c8a39bdb008737c6c6b6e97c361ab991d9435d2718b907ed20,-0x14460763b83b38b0a94ff57e736f26d9c6433efac0adec5b497ce440a5aa12824b5cdb17160c,0x105b5343574564750d9f5f0c73cd03243510f236e45fe64d5acf429d68019aa1444741a23f80,-0xbce63a7fbcce2329b191d84e44c2f1988d7567cd40af34d092c466abadd8d5befa380dae11e,0x79fc9a31658eb6b8c8eeebe1bb52a10c5be7c37559d4c64f6ac319e2013c67873df248955d0,-0x467273e6ce2faecb1fd341f01f3fc514eb6d752761d366f61ec1d206b8ac1887d9ac0e9c02c,0x2458b509df097eea301d33cf79f65d0bb1d150d79f3adeef719a6f96fbed27f6865dbf6eb90,-0x10baa539c45a62f31fd2abc360568379e0034c0662c690ab8e5c7b6511ea780a0d2dfbf6f31,0x6daf247c35a158f7db2a1b2bc9d2ebab99fa536700a5ff178f13e800778ab3bf4e1393ee88,-0x27ea1e0d5636bb79863c4faae859d7ee23f56149f16b52c6fda86b992ffc6fb233e02636a8,0xcdbc4551b6b27afc2ab2305e55ce6556be172a94accff6e4aaa44770bd4b25b80350e1f18,-0x3a7383b11befeae5e4ad76dcfc88daa0d7c1e99d854364afa82000a12de88a45ee6e39d5c,0xe946768eec7b3f9ce9450702d373bc6d7cda681e852b914b0ac4299dd0d6b9e4b67093c8,-0x32d0895158b19982133fc19c0858d6099a5b9a01b99b3b5b7c58296574fc540885d27078,0x99b48b2d7bb492d4e0d4186dde6f8111aafd7c5e76dbdb425a3271e9e37e8943305ff98,-0x190937eca516281c348053a91f3b4c19a055e1a74dcd71bb00a64d037baabf52707338b,0x37bd1906b095ac84d9ca96057ed1f2a9f88f14a80ffd7f87b9511396aeec553d619f70,-0x68f4c901aba142b7d26741059a496ecd856dade4fac47b2567210adc4cdb99038c13c,0xa534effb3ccb4565369d3fd5492f8252867b7f39a8bc72c09bc522b9ba815ddbb970,-0xd6648ffaae59cc9ccdc72eccf8e813f58c386fce0952177c52ddcfb6b0caebcfbce,0xe1a6043d98e232c726bc22a5192dffd078e261275993afd1989081509a8e1733e0,-0xbce1b104d50bee19259f217bb9a18893359dcae1fa317c0efe3f9bce88277c21c,0x7ad0053601b1459ff303e0063c251b14504a6ca7546ecdcfbc42b62c5c4e8540,-0x3c469ae0ed6fd3ef717f492e8114ff862057141de5984c148ec354b43cd3837,0x158e6520d296f0583ad0978c82cd0c2cdd1b326ebc0ab1f0c0de03132f3768,-0x56018ad64f2a4cb5a228848a1e09a1666c3cd880d9f2b48938cc3bffa6e0,0xe23de2369340bffefc5395b930b59612f19f4ed280857ca56ad7b2c6f8,-0x16cc710379fa0e15a5785eda9ec59afa15ef9b00783fbc87844ff0610,0x146c8550bef2db02792ed014269ca084a4d5bb3c1c94d74912bffc8,-0x8d9c32f4ca42c91bf669d647b85bc96d7abd566b2826341b01d0,0x180db3e3002d1ea19a0062b365b8e967a76cb2cfbae305d4d8,-0x11d8209ae3434a62c4423c019c8d323920e0260ae54abe9,0x19db76203681eb15783600000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 31
theorem quotient_ok_31 : quotientCheck 26 98 31 num den q31 r31=true := by decide +kernel
theorem quotient_source_31 (size : ℕ) : (coefficientsPoly q31).map (Int.castRingHom ℚ)=polyPart (key size) (X^31) :=
  quotient_from_check (key size) 98 31 num den q31 r31 (num_source size) (den_source size) quotient_ok_31
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_31 : cachedMomentCheck cache 58 indices rho q31 m31 31 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_31 (size : ℕ) : intPolyRF (coefficientsPoly m31)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^31) :=
  moment_from_cached_check cache (key size) 58 indices rho q31 m31 31 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_31 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_31
def q32 : List ℤ := raw_ints% [0x9f1deb697e1c5b2797c97962d4b4f91109e,-0x36937b68844decd88ccd2d79fab148ae36,0x125a4318cb440157959b70f40f7827cf2,-0x60a6e9670c4937caee006828f5f6557,0x1f14f2bd27e577d9860a996db270df,-0x9bedb20b86b034cf29d3953b1969,0x2f8e66c1596ec959bb005267cad,-0xe1209b6b4c7407875b143b534,0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r32 : List ℤ := raw_ints% [-0x34cc1d1e12a202a70b570701815d08ee51ee62091e8678fa9318b5ff0000000,-0x4dd990390175b702e49c3f4363db91d88e5b7fce0edac35c888554a8a800000,-0x36ae1090186774bdbcdde476416533c06a2c3aa154173d5e431bef56d580000,-0x185aa951b8fccf7dcb7e20742d0a74235a3702aa6089564eb6e14fd767c0000,-0x7b98ee8ccad13884b16da2d57e72fa651f1d3fb90b0b738576b62d62aaa000,-0x1db91aea859f84c5eeec6f35930c9fde75f90e39e0649296485e8f790a5800,-0x5a218b81b18e8b837dc9af4e7eae6e9fcd73eefbc44a6a08fb05ccbcfc600,-0xdd06c97a68053dd822ca36d0ea62380671ee7bf12b982db5f28e0b359080,-0x1be4ac132bf81fbbab0fe2ec4525e5accc829ec21be0e5ff6ed36b9e5480,-0x2ef8e0f34ad6f12d1d04ca71422c71fcc89c70bb9a70c09d8b143b4ad20,-0x4292eb85d697db6af09ab554ea26383804553d00bacb8a0263a4433460,-0x4fe9cff31a28efeddbac27cd109766c56ae04d8f7c1095aaf7688eb98,-0x5191799263a7d92545fae6e71a7b9a85b68d7140f7c98971bbde92a8,-0x46f0316b1b94a6135d10b9542f8c8a538e465d6f46a371ed6e4dd5e,-0x3492b1d4ee45c9e99fd0787b93f4eb26046571689311a92989cd64,-0x21255ad4285b27992be794f4a0b75e64ce45fce2ea44373b0bdcc,-0x11b6647f55d8aaca6961c27ff9b74255a75633f7b91bfdb443cb,-0x7f984a021b7153415476ad2491215aae9a57382366d426a382,-0x2ffa134494e3ffe1066e8639ce5f79caf0b5656e071642d5c,-0xee0fa0514f83b1635bbcbbda8188f143f4809413b38a880,-0x3bd347d23e093794824e0ba8ec05c31fa3bda84b7176ca,-0xbe03ef28411f8e7307b3c848f541387888fc9f5c0b82,-0x1caca2388663ffc8633ba3230ed6a5cffca50602ba8,-0x3173dc55602b4ab8d7db7bac25128390c6469f99c,-0x364373a29717bf5e1c30fd762d725c0f1867d7b,-0x1c77c03f38eeb1c8ae1bcd23eb26af058727e]
def m32 : List ℤ := raw_ints% [0x0,-0x473ac2af9ac854dbdd5501ad9e4911caa2580b18b672b809da72bab364a89c953e9000,0x819798250bbf097b02b2b5f6eae57668c8fab078aed2492ea0424d22496a486d88ddc00,-0x7238020ac36b6aae181560a99b0b8af091f1174436006641037e313ef61dff0f37039c00,0x40f72302fb018c2fc4ce4970a696f6d8d92fa088306e047b0ac9bba787d6f0b96d01cfc00,-0x1acd0a25da3d4704e96b8eb99cffa46535d39cf5b66e7ce9c264e5c564bc4658e7e9cee600,0x88b9f57e741f654a74b98397878ea01a54105a7cf94cf5a14582efa34d68def76a53422ac0,-0x230f6d4e7c64001e95c01e901fe9452348f8648cdca3a7d4472707e4ebfad91f6432d784400,0x76db3e388a08dd5f4a2ce69ef282a0ea9a1722473c3ae31e70d85829bcc927394e2f8a6ab20,-0x1537612a7da86665bb4deac53bf1c51ff6489f600a6da5f2822056c678b1572c431952a85600,0x33cb73859c5bad5bab2c6a12af06840a9260e755bb5c2eb630cf8881c8b6db98e66c94050650,-0x6d48c05955bd09cde1803c551443ee79bcccee417dc89769ea3707b765cf85bde164b1a81780,0xc9037b425a5c8bf4fd2663b120f61980e5955ad83a70b78707c69c6bbed91e54aaf47d987ca8,-0x14482740feb262f9caa045afc84873c8234c528057feb44842e138e46e7a64e91386d2639e040,0x1ce40303cd30cb6964e9786265d5d61fb1497712fabfd624f1eb4ae5afec2b0853c9db7252950,-0x2476e97217f374f5c29ec4ab751c2251801a610d9eea83237904b70d716f6ecc4696574bc0e40,0x28e96a68d52af89e1d5ba08e89f9303ae83c72fe6f21dd2102173dd6dcae98aae8e32c2300c44,-0x28e6f51f6a0c0fb6ab2b3f35ec3e55c766af24d724eda936b468582c6c3fc58b9c2b1ab7cc120,0x24807f1b451219f36dd5d6aa18fc4e3de3e2dbec76da60d5b155b765f116ea30c467e9fab9154,-0x1d1c16e9bcdbcc49b0b53d861424abb610cfb8adfd96e25451fef587c4623b08041f93ee44240,0x14c1924f278536e89701663482f3a3a524d3c653b1a457700f00ef94e6acbf05403f722fda026,-0xd3b8637114b83703ca8ce3224030d722d0dc0f2358ddc7b125b95f968c380fb8d2c01fd33cd0,0x789ef74102a21270cc2fef3752394d7675bbc2dcd06f8c9a6a79407d03f1007ed060d191c014,-0x3d593285384d0c376ee4f98cb4c58d23b665ef78f6f83848845139c68468b30036950643e550,0x1bcff20d79f4c7991e34c2b40935a50d0d2ac327c2135e1d893590f687b1dc56aafae28920b9,-0xb37342da6e35b139639d2a07a0e9fa67f918c54e65fe6d84cbe44943b29633a63c672759388,0x403386594e38637f39791f8a2250f2773f39f7d902d6e6ecce152159747f8ef852814c69a90,-0x144fddeaf87b5e997b3a13ad775b5cec0be162de99d20ddbef9e05341c11b2c9ab5decb39d8,0x5a92d5572fc1760ad29aa580c1c0c3e6d14607efc38a8effff9f3252c6b3b9f71177270544,-0x1622205e386313a68d7f1aa7741cd96e28840fb923542a2872619f49155e0c656555cc5dc8,0x4b77eeb8126041a017be94cf5a6243551e3a5a00136e844398810321cf1ddf028aa94b500,-0xdefbc5bb3884e11bc12cc522772f8f990a3eb38ffc336c16eb188329fba29da7ef716358,0x236ac4d2f072ae1f42e8b62b12f7eea11d80500311e1578587a2f861d8102316f7fcef73,-0x4cbe729bca1da329475fa80a48991b116a7bf9111bc458944dcce6c9194e8727ea9cd70,0x8c5a587622f6052b3a5bc7832d4477c69c3329510f485c756b0f8cc81d6e422a68f594,-0xd61128cd5fee909765d5d488c0747e94f171574176601bf091bf18ff754d105e10fb0,0x10c79fc35dea46a8067851f58629c4ed11e0fb37eaaa94c448c9b00c30526ed2b6ce6,-0x1104ad3c2a61200dbcfeb9817a4dc464b548afa32fb3c7c5aeb2da1c6b73505a1ee0,0xdaeb0090e4966887e608b4ee520594024bbb5d8c423330d4aeee9ff9762fb070d4,-0x8837d908f2bc901e27716236b523a318390dffe69c51fb106215601f08096a880,0x3fb7878414232c67344fbf9321cdf01606e8c0af978c9f8e9cb1b88959b2674f,-0x159e19d0c1f8ae4b7a7d181bb42902220017adb70ed3e2f4ecc14dca4761068,0x51677238d97e00c74d0a43106198e45f7c1775a33c642a1b46c497d787c38,-0xc8f0150aa7d741d7f877edd56961fc64ef7cb99e768c1e5b6d892780838,0x12e0b4d8249f9ad05409b4512112ac68aa22b29de87a0626b155829de8,-0xfa6d9c33387530d64e88ffd0bf0c80f47e889cebb71b6aa3f4467c8,0x639c7331e7c00a1eb7b83782e5ff75ca94b67b294e7c24540ee08,-0xf6224da8660965eda5e3df57273348e3e577ea8303580b7518,0xa428cac8f4bf1129b3bc771773a8a8654e7eeae6f830041,-0xd2d7b02dd3cd8d9bb39000000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 32
theorem quotient_ok_32 : quotientCheck 26 100 32 num den q32 r32=true := by decide +kernel
theorem quotient_source_32 (size : ℕ) : (coefficientsPoly q32).map (Int.castRingHom ℚ)=polyPart (key size) (X^32) :=
  quotient_from_check (key size) 100 32 num den q32 r32 (num_source size) (den_source size) quotient_ok_32
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_32 : cachedMomentCheck cache 58 indices rho q32 m32 32 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_32 (size : ℕ) : intPolyRF (coefficientsPoly m32)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^32) :=
  moment_from_cached_check cache (key size) 58 indices rho q32 m32 32 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_32 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_32
def q33 : List ℤ := raw_ints% [-0x1c77c03f38eeb1c8ae1bcd23eb26af058727e,0x9f1deb697e1c5b2797c97962d4b4f91109e,-0x36937b68844decd88ccd2d79fab148ae36,0x125a4318cb440157959b70f40f7827cf2,-0x60a6e9670c4937caee006828f5f6557,0x1f14f2bd27e577d9860a996db270df,-0x9bedb20b86b034cf29d3953b1969,0x2f8e66c1596ec959bb005267cad,-0xe1209b6b4c7407875b143b534,0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r33 : List ℤ := raw_ints% [0x9722ed7a41682cd8d346c7f4078564ad1f9bafb3e6e1dab4e93a101ef0000000,0xdeca9751dba0540df1d4ddfe23ff62a3f48d6d9ebb1895cec3509db8f2800000,0x9c70493b91aef735a944234ae6a99dad35a099d57430fe31421ef7630cd80000,0x45a7d3ccfe41b3873342551cae5ae53aae5e75bee7424e26ded3ceacd29c0000,0x161630b134af69ee427da6569390bb0d8aa9d0378b54b1be4f905d5d7934a000,0x54f4343e86dea68f9e64a2aaa9884b4e7a1c3386342ca3bfab2e6387c5e5800,0x10183df8f9f278c48a485b970d2bed809cb6707268cb57b5af2db1fc1a6c600,0x2773faf365d023a4555f807b5abf4c36358e232cfc548b8737a87a3b901080,0x4fa10959e449896d2a2b71c4695b2d54e21dcce646287f1c5954ce7226e80,0x8608dcb62893584d4e68b38a6637b2d6d5515037aad91b9f4bfa2b4beb20,0xbde057214f5c240bdbf0e7767493a0c34ee9b1b190c657ab47a1ebbbea0,0xe3cdf25db1ac583fa193f10cd621d84a620eace57eca33189701ca7558,0xe864e32c967e9ff09b83756c0dd5c76813955989a272c54224776d7f8,0xc9fd496aeb9042c9c0fc6ce74949190eeb3d3124a31f9c86c25d61ae,0x959a19f81031640d5d3307f742bb932054c351f1e5056756c2396f0,0x5e41a668f40779965a139adf8498c4f3ca02744e884b5268fbfc70,0x325509511f3145a6e7bab5356b94df2bcf7bd449b402b5d7d0700,0x16a4b7dbaf81f63daf054ad5cf52d7b5eb0b781067aa6b622c9f,0x881ccbc60fb185c1dae587e2c3dcbd3ec63de8d87c54e4b240,0x2a2c86f0fb763640a80cb3266eac1eaf01cd7d39b69029ad4,0xa9690f2036a12f0f481c7e5c8821b6701cf54f7f85b73b8,0x2198389a43ca082dbff6463b5918f1a1c4d55e81a7f740,0x5105a790c3979280dee9364e16a99c96e574892f06f0,0x8b8fd6e9799b1f9eb78f900c4dba78ced0564c575c,0x98ef7332daeafdaafddb17e719dba78e535aea10,0x501dfa10a7138c8b64ee4a59b252e5769fe2db]
def m33 : List ℤ := raw_ints% [0x0,0x92e9318a2f3d2f05787f53761676b4b1eed596e2f84c9b94528ca111ff9bc2f3d109000,-0x109cae3d9e21a28d56b2e0ed5b13a34381e850bf8e891b6f02a88bf16b76b3561ea495c00,0xe8e832363496cc36b1e4b5c819e2f8802641cf190b0643eaee1ed2e62cf9a2461b703c400,-0x83ada099d2dffa967e59462593a76ba1729bca2e5ea67a1fb442d40d34d7850bace1091200,0x35fc0c0baec8d2706769adb899e3151dfa68ccb8ba0d9f258093fcd66bc51553f579b895600,-0x1119fc7a61ea0c04d3a266532b73520190e106281d7bea21eb9ce699a800656dbaa5e9a0ea40,0x45b15ef0a5821e5c71e21454d3999523edd16cc436874f99c511b621a38ff1893d257477f000,-0xea9c78932ea131eab06922e246811774f39e7b9f7ebcb413fca83dcdd992e2c7b243971057a0,0x2992ffb4aac3c095dc24421dd9ced742063a83cbc2727c2cc710f0a783c64a2828794c003ee00,-0x64b96872fd4c31b83b610e0150c595e4c24f022d412abb573bc2fa089ac174ec26b204afd7b30,0xd2d7c037544a03c79732cf88ea99993c1484a64ffbe7958ab8229d954f8b9eabc62457f7aec80,-0x1809e0dc93fb852baa12d6a6140df171e754a2c26573d7450b8665da75aadcf551dc1dad84ff48,0x2679000dbc3590460c5a65a36c28e5d2827c9b08ce4e056f26043e3452bb13fecff7e23fb3fe40,-0x364f188402bf1b2b5cbe1cf3e1d96043ad7e186fd5bd7538def4aa2a50306d889e0e6a48fa2cb0,0x43e66514c9dc5f8a5a1b8708cc76742e402b064646ab585965a1a2eb2b0e4f1c4a51b2da7c6540,-0x4b6dbc31f7136751b24685ff6a236d96801d11317e8eef8289ac28bf4ab58352cb7c3087db1ce4,0x4aa1355797cdd89ce21f06a7a0e9643fb955b50875ffcce4732682425d9b41ea056689d5c1b920,-0x41e06f75ffb5fc53b9558c2f82e18ec87859ce62fccfc2e6022932146cea8655a04194aef3ce0c,0x33ef5df7893cc56604512e2d83f79f0655e4b147c58853100056046e7a1df56f635bd39d9de380,-0x2495f41fa2b46c68a70976e52608321b9dfc30802628ae81f229b741d29196cd0adbd4bd4f564e,0x17075056822f26675de7b6b0377f86bf8573cbef0fec83c4c9e565c88a9edea9bae570d96f2e50,-0xcf1be6ac114f4b81d9a60f680b8701d01cffec4834d1279772f24f56d9c97d7c2938b7a2a030c,0x67d91646f4e563a50653fd4363d7342898d47d039c06eb491440eb5f3c1b2aafaba51bcfa6e10,-0x2e601dd070a766aa38b78467af8a734eeff2122abb19a37e6b84f3404a19567665d57a4a68cc1,0x1267b6367f63399c6b46637d56f74c610e8ca0a0106c99cf723e8a2db685a3bf393094f038988,-0x67957ce12b473dd2e6ca6478eb03f6d89cd8b17ba4f166d0327c3fae81b961ea01013a518368,0x202f9a731edd7249026e858ac3a942f963a87415670a18f82aa51bfe6d3aa6a6e8b0ff87a218,-0x8cc9e1826aa1b54f4d7ead4b64a17cb782c42b5f72569d483be21e78484c3111ec50b69068c,0x21b49c3b1dc79d8ec40a3b4575029c4330d32e65fd48f21e91987a2aef7a0b8fa9be8ed2548,-0x706e8b9cc51e7a438ee6af3704f8749e57cdc979e2209c863dcc70e420c89c7301e6f8b498,0x14479cdfa3d54c9819fe469d474db795c700da2d5418c50fd9e70b693ccfd1944387b2db18,-0x324085509611ab7bbf5988b450f80bf54ae4fb8c8c3e7c65dbed640f64b770df1b996a49b,0x69f834f739349821a771e2631443f6f470a51de6f5a579a6fa389857bb61e04cf42b6d70,-0xbc34111367ae0135f81bda80b1ee1bed4928bd5856bc4e92fc37e4b480cff31fda593bc,0x11618764bb586eba19039835043f5ae9e8d3916d823b405ea205d2fda5d9af3358a3f70,-0x151022a3c653061c3107b844683503e48b43b90191d0cffe1df0d65ca76f46e05dd1de,0x1494a6834e3c92e9bb6a6d3e32de0077a064001b0ba2b3ae2c0a0e3d7d714c1dcdf60,-0xfe3789070d63cb56dcdaab8be8a48b71e8d937b44cc4f00a494a875396728bf213c,0x97559cf8ac5048baf62e62e7acad416778e61845d35800af5d1711245c610c6ec0,-0x4371dcc08bbbac181817196d3020207dfc0e943ec39e9b9d2112ea3d16e888a67,0x15b397fced8c818cb702e0bd0189142f29c233c076453b036293b5a6bf61aa68,-0x4d1ad271f35bf5278570dbebf941f10248833f4e13adcb8ff34ad855f6c9a0,0xb28b36cdd6a889d292b22cbe3c8baf6e07b8848e27d20f203fde9776c1f8,-0xfa260c10c2a1a067ab1c670ec5a0d5a85bcac22720324a94fb9263fee0,0xbfe9e22376dfdd6fb2b387567a20d5aec54425027cc060892162a048,-0x460ee86f7a0d24e1fabf1c7e6b1e5dd37a94027498dce535cb3230,0x9d615f3d72d0ef9dd399cedfa60af704c2d188f7f5751ecbb58,-0x5e5da241aa2740eaeb9d9d355de89b844d06120c2355e8d9,0x6b6eb2f11fdb3b3effd8000000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 33
theorem quotient_ok_33 : quotientCheck 26 102 33 num den q33 r33=true := by decide +kernel
theorem quotient_source_33 (size : ℕ) : (coefficientsPoly q33).map (Int.castRingHom ℚ)=polyPart (key size) (X^33) :=
  quotient_from_check (key size) 102 33 num den q33 r33 (num_source size) (den_source size) quotient_ok_33
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_33 : cachedMomentCheck cache 58 indices rho q33 m33 33 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_33 (size : ℕ) : intPolyRF (coefficientsPoly m33)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^33) :=
  moment_from_cached_check cache (key size) 58 indices rho q33 m33 33 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_33 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<24 at hj;omega) moment_ok_33
def q34 : List ℤ := raw_ints% [0x501dfa10a7138c8b64ee4a59b252e5769fe2db,-0x1c77c03f38eeb1c8ae1bcd23eb26af058727e,0x9f1deb697e1c5b2797c97962d4b4f91109e,-0x36937b68844decd88ccd2d79fab148ae36,0x125a4318cb440157959b70f40f7827cf2,-0x60a6e9670c4937caee006828f5f6557,0x1f14f2bd27e577d9860a996db270df,-0x9bedb20b86b034cf29d3953b1969,0x2f8e66c1596ec959bb005267cad,-0xe1209b6b4c7407875b143b534,0x406b0b9da22ca0c7a23959e4,-0x11c350f5c6160c0faf8cec0,0x4b34cd3d76b7b2547dd4c,-0x1300f72fe00d6e7e7955,0x48efe13095cc1d78ed,-0x107d858b3baefe77b,0x37badd45401ce0f,-0xae0374d6a4cfa,0x1eede658af3a,-0x4e98c06cda,0xadcdd236,-0x141aa63,0x1d40b,-0x1dd,0x1]
def r34 : List ℤ := raw_ints% [-0x1a958313faf66991ba76eef5ddbb2008e4ac085f28f8a6e7ddfc45d10258000000,-0x272d8232f57ca32bdad680a05d16e7f61e78cf49668ee84c73af7acea97e400000,-0x1b8090d10fee97b1cddac24901aa3d9328378c0a5933a48c74a13bb0bbac5c0000,-0xc3df6b06afa958e6d7f4a7cfb0a81dba3f1d01cbc8548a01d464cdc3fdeca0000,-0x3e16c910f7593dbdd8be38c7e313fcf6d368db30dc0430d195b163b9cc1ab9000,-0xeebd6a69492d393491cc8b8cb0e6952eefd1afe694dcaddab6310ecc61c44c00,-0x2d36c41550aa9dc83a0be3a53c2c8f1b2035a16bcb9f30836feacdfff5cf1300,-0x6ecab7f8b273242d1edf1341ca51ed49084503e67cf19713d0ca954a9eeca40,-0xdf866195aa70ea48c95c49697a1d141a8f759e9f289cd0514518b6d1923d00,-0x17815fb77265916bb5386d3d77371d95d502750864d823220aec9bc97d8e90,-0x21487b30e0a9dee032616ebe423f45796e3c059e71cf0a7b489f77ad4f640,-0x27e985c23816b86152dd57a0ae4730b380bd2ec0cc352d728dea312d102c,-0x28b1ff52da9ddb32d972e7e1005cb360ac3d749b4ce8b37d9a5e5667690,-0x2359fe23539167a4e961d3d30dfe863d9e8a99e3fdad331b72cb6c2bff,-0x1a2adc026a803d4c52b2de2cd722d0c8dd837fe512d5fc7b5dd7314b5,-0x1079f15301d6792db02e322bd2289a286e79d12ff64d02b55b39d762,-0x8cad37395c77545d0ed76abda3b80052e6844dfa266129283b27ce,-0x3f3de48550a7956da21df04d7df95cdcde7b834a1a5000ac1f4e9,-0x17bdbe0499e70569d9d5692463bb59936f08d485a33c92e75126,-0x7599809d690abe994b46e055bd17cf9ac97ecfe0b577489338,-0x1d7f79adcc7e74a1fbb5fb6d57e80df6fa1516c8201238a38,-0x5d8088208d9c3e37b13d6599fcdf8f619db44615a920041,-0xe144e39f65c9ec3a71aec26b223c82f3e8625bba5c73d,-0x183978eb18af8e75a7d86b3bd96f6dcc45d1c05a375a,-0x1a836cb50f5a4c5533f6cc1ec505914d277389b412,-0xddef671d0f0b5f33b4908e5a66af031a78867e7]
def m34 : List ℤ := raw_ints% [0x0,-0x12f00f62d016e30fb48869c238e54d4aefc988734201e00e1ea420c351f314216df229000,0x22136ea0c56163ec79849eda99709ebb3bef268b15fac894f57ba0a1eda4d1e19f3374dc00,-0x1db0f8d928f7f7d027c6ec5b18d0fa80d41d4d06a984d770deb8604ce1a64aadaa0e9849c00,0x10b02c2f5ef075fbaee1fa1b5925d62da2ebefa8ecae6a4c534ff41deb34ba864f8e9e717c00,-0x6ccd1818ed66351d629d803efe9adf50bc8edeb32adc64b0cd0c92b779ff9fcf482634863600,0x223fa2891dff6b6cfef0168f488417d9d7445a1611bff15a5c93479aa67ba351151f7693ec6c0,-0x8aa729a22242ca5a118bba3cfd4ec5b71b2689dd05d53e7b6efbf76e0104532cf939e7eb41400,0x1cf8efa3502e63a2874549f3a5317cddf012a3dce7c3bae297c90f2460701bce80754190f49e20,-0x518efa5db95251e18e71f080640ee3cbeb446f0efb6a0ae149f4715beda8a9785faa5639b8de00,0xc420465f8e404c393d37f8728f3d3929868d0e6ce8f6e156dcd7c912635c2241d644164227cc50,-0x1975b20b3f4b21585ad481d62bd1cf3249322a8134efd7b879899033e0fc7b47935d4b74dc5ff80,0x2e11124aafe908b55a7399a4346809260d3c9d6287274840ad26f4ec695e02fb6d59964e23e3068,-0x491a32a153dd63a03d6d69a00ee0bf3b0c3142f9e588a8823aadcb31071f8ed7e34798ab3e9e240,0x6646f7a95efd48d931a21ce9d86da373e1f1028ac296d722ce4d898f07767bf4245e0602cc507d0,-0x7eaeff7c06efd934fb21e6826d90cbb90336d02c819e5baf463755591517e6276683c027d1d8040,0x8b5bab4836de7bdd43a40be1a9eae960808640607044bfc0fe666d1bbf8581dccf5c65ce6fe0f84,-0x887889b2bd118da1ed0ced1621f31420e40553893ebbe1105fef41f9dd328dc25a3dd529bacad20,0x772b44bdc937a571b25b051abc16071253ed6f18c6fc1e9a79700513993146b9ccf164a77722554,-0x5ce2bd3d76ac3d06096264f1517b2e15e0966a7f687c0bae1c2cc88e3bc4719605c73649d438640,0x40a747d1bab4b5531b12542081df500fc59213a21cfbc023e62ebbafecd8385ef361a8c0135fc96,-0x282f09aa2262b4323c0c9daf35e4da03b2cf851809396afa8bcbe29430f5edacde5a30afc6f8350,0x164984cc8a8e5b17621536c0a8ed4af0c7075389f2bcd10a1d88a8bbf2511cdcfa4329199332d34,-0xb04a76fd07e307e32b1b96c5b3384b6966837db0959b27e203d348325c92b13bbe78f00501f7d0,0x4d8e0a5ce6c0861e9dbb548e999b9cc16e052bf26eadd22cf9f7fa1ca7a6aadcf2ba591e4cc449,-0x1e4b2358b0c9d72305bd9c26105e800f8e55e0cf939635e980840160b2db3abdb5a85393c26688,0xa7a1e8273180292b84b42ad3416630291f93f00364c83dab12716d5eff1b696da9dde62212cd0,-0x332860436919b2a0a3e1217e3558b400450078ac427da788c433ad0674dd9c9956fadfbe570d8,0xdb84a553bf0e5f9273fb84e9566f5ca01fa760d984b64a2e6043487a1d8bdb69d08215b67734,-0x337c717bda8d417e2fb5318bac08c3174f6b43a0bd86ac7558beff30497216057c2cb87c1548,0xa8029a4fb353404bddf3f8df6cf345106fd9245135c8945e5dd35a27abf922d22fed9c839e0,-0x1d9943a54b73afc0d8c389b80359a86ef83c69cdec2ccc49baf053856174692b49fe0a82ad8,0x4782593f7cc7e458913bedb25e305d8f5431c8d41e6610cbf03d048026c96c21d8d446f703,-0x92bcac43d308390fcac3463f28e1f4a13c4f06dc4286642831532183a395d106a0a8b5b70,0xfd0b56761bcd53bb44d8a7c7a4e041b8a693cc120cf78cb66939eaabc57f0fffcb572514,-0x16a2f3812bdf24fc9b22068ca4340ed75567227c56b93b61093773b4138cf1b642d7fdb0,0x1a803fce7fb211ae46699455521f549fd0dce02deff15479234488ff44b0dcf65e687b6,-0x18f0de5621b4dc6d2351468e9b665e2dc99fcc1e37028d0626570db1cf9299ed4d8460,0x127c03d6150c902f199bf7905ff966af03ca021f4e00a33f262a204cb25c8d50e0bb4,-0xa8641f41efa516c83dc9676e6f5ea7cce24a2fb5ecad65d859e3aae1c6a4f713a00,0x477b42d6550af5de33b72a1193fa44c74551e81ef152294433a2e3c45efb28927f,-0x15ce970389a2f7f2c4cf79081a4f4cbe19989e4b80f402f1added968830ca8b68,0x491501f1c4c16e164c697c8bf151d0f670242d09aba083014fdca25d78b2c78,-0x9eb5b4ece3cefd8b41363b79f25767cf9c5e14bd71a00038c6fa36c54c738,0xcf3442c0daf65a0d88190709d412d384a183c16d1760470072b39ded8f8,-0x931181b1385e8f42c49efde66a106b3772e3c3746c5c65b5301f66248,0x31440c00e0db4500442ab186d03e342dc8b06acf1a550b9907c1aa8,-0x649bd9ea655b4ea662f1aed14a608b04af9dd962d9238cb2b798,0x363bbcc7dfae79e7aa7671a3527d829bc71611d044fd3dbb1,-0x36bb3487bdf284d4a9840000000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 34
theorem quotient_ok_34 : quotientCheck 26 104 34 num den q34 r34=true := by decide +kernel
theorem quotient_source_34 (size : ℕ) : (coefficientsPoly q34).map (Int.castRingHom ℚ)=polyPart (key size) (X^34) :=
  quotient_from_check (key size) 104 34 num den q34 r34 (num_source size) (den_source size) quotient_ok_34
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_34 : cachedMomentCheck cache 58 indices rho q34 m34 34 6838148142154569849030079257600000000 33=true := by decide +kernel
theorem moment_source_34 (size : ℕ) : intPolyRF (coefficientsPoly m34)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^34) :=
  moment_from_cached_check cache (key size) 58 indices rho q34 m34 34 6838148142154569849030079257600000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_34 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<25 at hj;omega) moment_ok_34
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30,m31,m32,m33,m34]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<35) : intPolyRF (mz e)=rfPoly (C (6838148142154569849030079257600000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^e) := by
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
  · exact moment_source_33 size
  · exact moment_source_34 size
#print axioms moment_source_34
end
end CatalanCore.Li2.NVMod.FamilySource.V8C34
