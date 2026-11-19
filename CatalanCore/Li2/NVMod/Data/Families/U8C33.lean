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
namespace CatalanCore.Li2.NVMod.FamilySource.U8C33
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,8,33,size⟩
def bases : List ℕ := [1,2,3,4,5,6,7,8]
def indices : List ℕ := [9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
def num : List ℤ := raw_ints% [0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def den : List ℤ := raw_ints% [0xa9e39e257a09ca2d6db51000000,0xe8e8720f6375414ae8a15b80000,0x98347cd3235f404cce8c4f38000,0x3f1d3c1bc426510720e1a525000,0x12a61c83bcffbe93dce721e2c00,0x42e16209e7910298c75d7c4b00,0xbd1e08350fcca0d22c8780cc0,0x1b0a7096bf015d9752fbcff00,0x32f4b4d588862fc5b6df7430,0x501b9715f423bc20bdb2500,0x6a0548699e811e6c4649a4,0x76dcebd2d366e8e061dd0,0x7154f975500d1d1270cd,0x5c13b95af957352c8e9,0x3fc0131644f63ada86,0x258c1458f2b4d6982,0x12bdd379c8266093,0x7e15248ad9b79f,0x2c432fdc7c788,0xccfc60b9ecc,0x300ed4da03,0x8e539817,0x14039ee,0x20242,0x20d,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0xb,-0xb,0x3e9,-0x1b5f,0x8f,-0x97f,0xa16f,-0xbfb3d,0x14b1f5,-0x75b4217,0x4e0139,-0x192c265,0x485eee26,-0x242f7713,0x321567b,-0x28b1643f,0x25dff73,-0x1338b3d9,0x12f5c113,-0x3217d6d69,0x2ef7dd47,-0xfa7f46d]
def rhoDenominators : List ℤ := raw_ints% [0x26914c54a700,0x4922b2e10,0x3b33c40,0x60e058,0x1e480,0x5ea10,0x23dc0,0xee,0x1c0,0x46e,0x1068,0x717,0xcc30,0x35a,0x888,0xeff1,0x5b00,0x770,0x72c0,0xa18,0xa180,0x1a7f0,0x10b2b40,0x60038b,0x1a2f830]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-9) 0:ℚ)/(rhoDenominators.getD (m-9) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 8
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 9 34
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤33))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤33 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
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
  change m∈Finset.Ico 9 34 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
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
def r0 : List ℤ := raw_ints% [0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0xda7c219853e377d6a1f968c295097af89000,0x1f712e8fda6f9f0a97a0bbbc2f213489a25c00,-0x2346445f7f922857a6c97a7ce246d5238d89c00,0x19b14d882efe115fa4d6624440c872ff07011c00,-0xda8a8f1e3e3896a156325fef0969c743f5985a00,0x5a63bf25847a7103fc420026faa4149fd26d44ac0,-0x1e467c8f1208ea1136dece3e22b760a5ff962fb100,0x8709ee0393ecb9ecb31ef689d9807eed8195778e20,-0x1ff550add1cf0c28d15217d301c55d140d98b5f3800,0x68455c455c57094d17ff932f2539345e3df1d581550,-0x128887c945c9457875d9b383b5d782adbc5f995d2fc0,0x2e5be3e4eacd5e50009484f9ce92a9ffda9a472ed468,-0x66bd5c2342ed1aa7ac591f01a52adfbb12707acb4fc0,0xcaea6b97367ed0cd1fdf359eb77effffb370aacc7ed0,-0x166de23010a9edf5b4746c51343613a212350388b1400,0x23a85f483c7e1d0f577f47506f5d0fa275f945dd25c04,-0x331e037affa5f84677dc4f9255c9fd1efba6243f3b120,0x423e0a387b835c2d31175da2b50630e33e83daf0f4d94,-0x4dbfdff4219f29ba963e400541ec84f1ee810111229d0,0x52c5711e694d91c1eb0320b015c7cbe8fecfefa0f5a16,-0x50011d9695b6481495653cbee91f77154970a54b27130,0x46403a264838ab60c104d9d6a556da129c142a1847df4,-0x380cc090d8b144163b8528da3206e5cb6318237509600,0x28a000946950a9f950479ee4bc21ba2579c2ec72d0f69,-0x1abbc5e9c676389cc9bedf0e94a20b28d8ec846db4048,0xff4da7ac8edfba93abcc3474ccfc3835f6f33d4ce990,-0x8a062625604bececb2ed5d0e18c862720c94a2e09b68,0x43771a7632cbe7704d85ac0a2f046fbe0fd06bfc27f4,-0x1dbf245ff267a731a29d9a6643d29a6256bf6a51dd68,0xbcc476ce030ed0902167d151b318740ea77c3836b20,-0x431de075ff2298821b3ffe4ff3fa31a313ca7aece88,0x154e4de988709fe3d9984c955d648989069074e59e3,-0x602607f1f9b98eb7e92bb17a569ac240b0b0eb53b0,0x17f49c567b89aa6eccbfc71438ceb3ffc633a9ced4,-0x53c6da0561653f206aadec437ef0313193d0d28e0,0xfee6fb2e076739504b8e148c54e181968d3c27b6,-0x29c09db21e49a339c0fa4dbcafaeb4119a4c5600,0x5d1ae629afa22c75b94e3bf2f55dc6979feaef4,-0xae013a1f1445a9f8bfe7dce6369044aafd9e10,0x10b6b5da3b8ffbe1a75d8d83f2a1d3dcc1dd5f,-0x149d35b38faac2d5f022d7d60f015e3102368,0x13c27ebd4f67e4727a2233b6e152347c52b8,-0xe1762c944fdd4dc927fc56d268a862dea8,0x7068f0f51b3bdb47b0accad3ba9addcb8,-0x23abca6b399ad079d4505a2f37320da8,0x62c2fbcf92474270f06163bc337468,-0x6f731bed913746bf0089487c95e8,0x194d4223a8bbd8a406e9c93851,-0x923106df4fe347d73fc40,0x44cbc6ffad1fa9563c200,-0x1ac10646fc36fabdfaf00,0x872d98fadf66a210be00,-0x21cb663eb7d9a8842f80,0x66fe2b69cec819f4600,-0xe0b6302cabe3215b00,0x138a46f8c1089eba00,-0xd06d9fb2b5b147c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 25 45 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 45 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 58 indices rho q0 m0 0 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 58 indices rho q0 m0 0 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x1c2a0054a2d05272aae12681153638da0a9000,-0x4026ad6192fbc3bb11d9e5afdf17a325cdadc00,0x472e8bcd541a2b050b11bbe476b7e5d46a7e0400,-0x3344a2e2ed3725d1043b7e0170808ce9108010200,0x1af2305839d867d1479d765cd13a118896a5077e00,-0xb0422f30c690cac06263b91ed2547f4466bade0240,0x3a574d17822c9313baf9be7fd9dcaf1a532e104f600,-0x10118c266af2b1114c2c73c27b52f0488eb93066d6a0,0x3c1969492abe85d6c3b28ff275ea4ee0dfbf4f64d600,-0xc1a2f92baac52e1bbb6c0be67e7ba7711d3255269430,0x21fa6d4fa0850c5478655b0608e1e937448fe5a9f2000,-0x53e28a3b8eded30c2131df5e47b1bf94598d323de1208,0xb76d824353f5fa667717e42790399c2a800412e182440,-0x16558026f76c8d93f249191a6e5afb0a7cd265d58de130,0x26f2c6f5c5eed705a6fd56ebfaae60ca06351a064a76c0,-0x3d092c92e3bb6ce899b073c42ca6b3544a5261507144a4,0x5637f0a3816cafe7c5ef148a31176d7cdef6be6b5ccd20,-0x6e0ddb2a3b5bbaf3f4c8d0e0905f18791e3d1960adadcc,0x7f2f1286c59c0ab3462cc548f320e7fcbfc924a69dae60,-0x85420ed36872933fac04d30ff0ced3ef2429251cf17bfe,0x7eb5c7917741508f5d821de9804011231b64a856fccfd0,-0x6d66dbdaaeab9b632e4ec335b7ca8bc0b981f47b80b3ac,0x55c85a6c5412d833f3719b48155b955334ff39f7a4b0f0,-0x3d121ba653574b472d99b990841c31aaa4894930c9d771,0x27735fa1c4a2d5d3570572c613bc90f0a0e737b6789a88,-0x1719b549d4c4a66b9bbef5e32949cc8abcf7f0688dd768,0xc3e57b719231e83b87fa3977f7db5fc644a39dca2e378,-0x5dcdbde2c2b581438e46f8af82a28dc0fe32caa3e457c,0x287c3f01e4a04215deb38486fc18caafc4c8f978129c8,-0xfb432ac7c760bd65fb0c5b6bafa1ca2e294756d38bf8,0x5749d4ba22b207e016576aff6ea883e1508ccec44e78,-0x1b0ba3650d9ad63227dbd26a832af0fc99fe14f7148b,0x76fce136237168fe6d7cb63d59e42e2f861a578f770,-0x1cdd66d996d204c7a13ec934a7bb3bc0c5691033a7c,0x6224ee1be72deebcbc41c56f2fd6409e71aea67410,-0x121dbe47b115c56404bd1b2225deb91a7a003d3eee,0x2e0033f6c10b70715fd30935e638fbb05a5c7d1e0,-0x632d4e9037f6967bb90f6ea167e6904ff38c4a9c,0xb2c4ce830aa8328868711fa30464a66aea7c960,-0x10839bf13ca4ed3a27de35a91ac4e8b43da9777,0x1385a481be23829712e194be640ff3162b8368,-0x11dcd8f8bb2572ff4a915acc25291cfa3ca20,0xc19509d4aef5a37bc73f61ff1ad2051e598,-0x5b1871649d77025190b9284ca6c81fae70,0x1b10a985be7ef19f3e70ea7044ed149c8,-0x456bf750b97d82d4831b1c30d1d4050,0x479154d93eed64d2627a6dca9baf8,-0xe93c161c34935ba9980852f669]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 25 46 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 46 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 58 indices rho q1 m1 1 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 58 indices rho q1 m1 1 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x3a16a0ae8fcdaa0c80705f6a3bbfd541b5c9000,0x82ea404b00125b1c470e2eb237e70e11d5d65c00,-0x8fb3ce6cb0728493f8d460bbc9845c71d34665c00,0x665e4d5f1c9df266a5123d4c52b9ede1153b61ac00,-0x353457b101df74b0bcb19fe576b0727f91a6d809600,0x158117d6fcbd73fb257787acad01823fb234100256c0,-0x70914bb55e59c7b6ca15c8b1e51bc7bb990838f51800,0x1ea34f0b8ccb3f706bbea5fe26eb3639e8c6285948120,-0x7136184c5ba02ddb0333549e65f822f5ab98e5dee5600,0x16846adb5b1f98f842272d2ccfaeeee6ab237304521350,-0x3e6cdc653f70fa49a621e9be848089ee98f3fc92f3a080,0x9822f1b564ab3cc08aac1cbd1808e9cef1eff68636e828,-0x1484e05cf2fccc53acfa0cde1215920a1deceb1250e6840,0x276ff1afa9d7c6459c88d05ee863f4fafb35732be73cb50,-0x43d44cccfa1119df85c8b2337996755a6fca5defe237140,0x68cc3a7d77e901cf231673dd4642853f040a0cb988b7b44,-0x91e5e804df795fee09128e51a4f5f4f65714cbb4aa81d20,0xb778fc2a1b536d9f419b114685970d619144d797909bd94,-0xd0cd9897e8828c0123bb7638a0b2f0f7d923118982aba80,0xd75a7811a64badd8a2fc50c1f2468c363b33eb151ce7686,-0xc979fca6dc831c293410227b2e44152d8b9e60e4fb00ad0,0xab12aa0351fae2f6b1cb386d83e453c1fb6f55cc8cad894,-0x83d91d6d5c92ec60dfa3434e82e757488b05e22644fbf10,0x5c3611fcd8ac8b3dee4d2ba560a9bbe35c63da09d09b5f9,-0x3a7b6023d4c66f294e1c36d3d70c2164889dfcb96d85288,0x219950013a95424ddd42a596896ac9c00fc4073fa8404d0,-0x1175cb9bcaab0b8c41b04a8fdfe6a94b53265e1c5c0d718,0x830f70835fd4f583f5b4a3a3f463e4b36c88c5260983e4,-0x375fb582d7d58df420a0cab78818ada29ea1fc898bc0c8,0x15020943681a1b0e862176f8fb3c55296005da96dab480,-0x721921efe3c2ff13891a09f93185c46c00b2747421a18,0x228193d5b2bbfc74c13280bdcea982ee240444e889e73,-0x9400b4ee5652aa89e1f1fa59a26c467a25fc8a26af70,0x22f4e341c6d03104629265f48abfa1a31c50b5c26654,-0x738d3e0c4094f439a1e853724f7a5623d8c12971070,0x14b3a9cc3815100be4435b3b13adcc6cb9921655886,-0x32ec64cdcf72619e399509b35d3fad9c2ba22b02e0,0x6a21182a7eda93bd27ef33c44953257b33e3fa254,-0xb875ca36fee02545b366002786fdbcdbe5803dc0,0x1061efd1982391e11b49dff9366e467133fd338f,-0x128e1943f90dcc54b72f1027fbbd5cc72f9e368,0x1032e34ed1f8c5d470f8670c0daddd71d2aff8,-0xa6a3eb645bbdefb5b4df4bd53b3036a718f8,0x49f6c3e78b56e196ed937efc8ddffc485c8,-0x148f2e50abaf6f2ee66d029e9a911a4ac8,0x30d164b37772cac35a2fb37a7fae0e88,-0x2df3162b644adec5ba8fbd2fd5a858,0x865645df9b359a7717f63e166c1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 25 47 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 47 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 58 indices rho q2 m2 2 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 58 indices rho q2 m2 2 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x77ceab6808982eb9c8e7c4cb1b3ba7d786ee9000,-0x10b3819fe31fc0abf3706ca3e8ad9282c844a1dc00,0x1223b0deb3c5b4fd2dc2ec85f2564380def5b9d0400,-0xcc8819d1b22b59732e2d75ece0b472edc016abbe200,0x6923dfa54270ddae3710c0194187909d048527cf1600,-0x2a05a67f82036255ccd6ecc45a5270c8c228c34658e40,0xd97882f4aa062969ac2b988839d276fe2d9e7cded0800,-0x3a80d4cac21433968e3a2906b87cf89ceb21ad39d7d5a0,0xd59e1b0231f19177e4f41e2ba9d011cfb4926586721e00,-0x29f9485c429b7d672b07fc17ca681be1b437a616b5bce30,0x72ed3f33240f51132bbde23208d55417f8c5aafd2797280,-0x1148c42dc5adddfb7d46c592134b20ccd42835c7c9076cc8,0x24d100ff7b1dc014e83c9df6d77ecedacf6368ad9a3c8240,-0x45d2e492ba5fd0e98a3f73aa52d8280be9ddade890179eb0,0x7676956cbba06fdfdd23d85cce0616e693185dd8c4cea740,-0xb47bcb9d6c9f20c14406fa061a55b0bcb3af00678454c7e4,0xf7aecf4afd751e807af7f10670ea4306c19c56268edf2d20,-0x132e8d7e5443b30c033ee9a07a20aad72fccbdc228053adcc,0x1580697dd91834c4227fbdf54246efed16973b90a81160d00,-0x15d539565498fe6615936ade50e1a25c383ff8076f567f72e,0x1419c0d1f45ee8f2cc01c4f5ce6195f774633ab9574758350,-0x10c9809fd2b7ad70a0861d5130214212acb1194aa9638eb8c,0xcb80af13fb468017f8b2ef806364ab855cebf290c47ebc90,-0x8bd5c34fa6cbef706f0ec6fa651e3d7acd30195c2e4d2101,0x5714e482139fa636cc9468334cf8be9945ff9ef1a208ae88,-0x3117c5be3ac2ecea4ce1f9d28cabea266ecf1e73a370c228,0x19042ed76d18c222c0557bec82df7e6e3b52dcec42f79898,-0xb7fdd675c26f8a3ae786660de9fe9fd702ea1a1ae9328ac,0x4c1b3df44803b92ea6cfe3fb30186d12bc44e5af57e0d48,-0x1c3df682180487f801f4ef87bc4ac328b772f958c5fb718,0x95e2500fa8a1cb69d4f33bededb981e7c0b5dc42b0e498,-0x2c3ead46e539cc580eb5a5a492e60ac20f19a402a8f59b,0xb903004f7456f0a21e42685079c639901809fc6c30b70,-0x2a8b3ccbf4c3739a297647c9c1001e30e50d28b81e8fc,0x88b6712468ea23cb0a45f39f3107b2bb116662d3b1f0,-0x17c516d90ac4224ef25f5618fc4c7e9310ba10284efe,0x38a28d7b3b7472515023f18e4ca48101007f1467460,-0x72133d5363170d90ea659d10ee18b9ae3b7c962cbc,0xbf222a9074f07817be20937de459c4599fe30f440,-0x1050b94b67302b3d708b15302488a3ec4282325a7,0x11b29e9beef00cc80bc2952c8d984a9b60e7d368,-0xebbfa7be5e715658a1e853e362498b0c43fae0,0x8fcce0a15c2367dadfa0c35e0f31c36c7f978,-0x3c29779130062f2e24579c47ae527c897540,0xfa24ed629bc8edc1c2430535fa43f6fa48,-0x22575301ea6f408a55d69d904fdbbadb0,0x1d7f04b1cdeb29674678f58a273f3d8,-0x4d5a60029854d84b2b1444da4b59]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 25 48 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 48 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 58 indices rho q3 m3 3 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 58 indices rho q3 m3 3 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0xf71a418691b9e05f2e5e05e2e82b0a2c864c09000,0x2218da0634ac433d42a7114feed79192b4758dd5c00,-0x24a6a5b8c979f3e586194b97a16c03e31d1c75375c00,0x198e92eb77261ba65e9a3804c886df2ad3f8ec0b66c00,-0xcff26d224283127a8acbde605fa61c3f7efb0d3f3d600,0x5233c4a8dc263f6042159f20692a5a89204ab0dfad72c0,-0x1a4a8dd27b61a4bac00726b3232b27331db84eefe976400,0x6fdfe375ddf912a582ccec0bf5ac1063333c07598fc8420,-0x193bda402b43cc7456d6a8e3324c2d83609ba7bfe6feae00,0x4e6322bb6b7d21efde6056062dfd52a3a6e3641846e23950,-0xd404a1f3d9f7fe0626917dd45f01c5a91eb6598ae7d3eb80,0x1f7d429b9ed1f52ac6b065fdc86bc052a1e509e91e8535fe8,-0x423829dab25e0808f61dc1e060f6eb1c3f7baa8270fd0fe40,0x7bf2d54658100b9d1c1db547f43616d3ada243bcaa02fe1d0,-0xcf7a5f638590829a877c759b4d03e4569275acdc817097040,0x137c365ad50967c41aeae30e898833c181c6415b4b79723684,-0x1a5d07d50fb97967e284012dad71c3a57a73f05e40da51a120,0x2031d70ebf5f40975d03f9be0e14029417dbaaba92d0e73194,-0x238d1466ebb5f4658f0a92a6154ef574b22286bd44e1198140,0x238bc44ea62cd66e977a110820e7ee49e9a929bd12fad467f6,-0x203592279da43f26e83631efbdcc90a171ab9aa2463856ae50,0x1a76497d82b4eb18cf86777441ac9993c278e3c80239dc5bb4,-0x13b66410cfdbd2bcc97b0dcca3888761a356be3cd8e6ebb3d0,0xd4f62262605bc3e67a354d56c8c31a39b28043439938ea789,-0x823cf9472e57156e00263d2476e6cf7214920ca989ea89b88,0x480e463e545d992ba9314cd2b4b60924105a4fbbac6d10310,-0x240217de5397270f376ddc802026702bf88a2485f299eb6d8,0x1038429bac0780fbd02310c099d2144faf61c43673a8f54d4,-0x691a0bdc67b06ca964e0b9ec96972f90d9995c590da79348,0x2626a5fa14ef07a13c16b589581d94d9c4c0bb3d342fdb60,-0xc5dabcb7aa5f15ee956103cd3dd5d3f6f4383fd7b3b1fd8,0x3902815c0cba6f1951cfa1d8d938636de39bae2adb14a03,-0xe867c7e18fa506ebb7413da1144ab36361ba2b3c148970,0x34077ade79e8b41b6bcb8c6be91b88068da72d89bf7dd4,-0xa285be28964c5ccdef24f6e96a301918d498bcb112cb0,0x1b6b9939e3bd11068d9a98b3b050c82157428cb60a656,-0x3f45bd74ac31792e8ede30d7d8533e64264ba74abb60,0x7b25a91ed2f67aac81b62ab4c55b2cad83a3bc1b734,-0xc6db1c4b545b1f4b0d1462708216fb354bed4c9800,0x104f37ef60bce774bb7cdbba17f7c3581133a82cbf,-0x10efd42c42214b1164d6330b3f6d873ceb14f7468,0xd70e1f1c2f0188961a0264fc1499699acb14c38,-0x7c612ea5ea0abe96508e913ff4e20f8a1adb38,0x31048a7182e6b0c9dd6665316c702373735d8,-0xbe676b1e2ba168dc33ee7ce8e024184b648,0x182a16e1d2162274882d50f5c9753ed128,-0x12ee3cd5aa8b02d4e5e8bc2db6cc3898,0x2c875f6085d6c5602c12728511a31]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 25 49 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 49 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 58 indices rho q4 m4 4 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 58 indices rho q4 m4 4 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x1fda627258c8f5ec44fa1ec23fed8c4fbd4fcd29000,-0x45a07f05ad18d6639296f6309a7fc30883027488dc00,0x4a15ac51b4ee3531668d8804bfb84139176dc95640400,-0x33206c0330d04bc43feb4edfa782302af4212f683e6200,0x19b9eb5bbe88191a4761a3267c6fc83bdbc732da9364600,-0xa0f7a8c6eb529aaad7d24eeb99040d69052a4cfcf06da40,0x32eb2eed00f3d7cf4dfa502c26715a34503512a7809ee000,-0xd63e2cb223911abcc7152e7aa52079f0771d364311ee1ca0,0x2fc53522b15d538144ff6b3ae512d9dae2c5151fd3a97e600,-0x92a8b3ab3bbc9c3c6617b5be4ce0843da6018c43031f96830,0x187ed4bf08a73c47f754d75a53576c1b62fcb8e21db59e0480,-0x397f09fe2b6a2ac36fd1a74ed66aca08eb16f4947e096b6988,0x776456bd3e166586815e1352f7530fbe3be46f8b2aa97dc440,-0xdc99c6689c025b8d3cfc5b7fee864d3de4347d241f5e3a1c30,0x16c641380134f8755d9ac66c6628bb44ffae2e80c73b1e99340,-0x21c20e2a1e28059a004081441e09d38695f9c99f10b3e066324,0x2d09f65ec35be9064c5472127ff219a1b9d041fb9baee510920,-0x3636d7365cb59e5967a3e2409d69cd8fc030f97e4c479c505cc,0x3afc2dbf5be1e3d8306516b3f19fffecd45ce97be07efdcfb80,-0x3a15231172076c18343a1faba544a173aaaa30f04cc0f9da0de,0x33ced3c8e50d8fb510a4f5aa45e4f4708c3bf6fe9af663dd1d0,-0x29e096039ffbf93ee5211cdda1ffbf5c2cb2d7051dfd212db6c,0x1ead12d317021d1145ce78acf547a9c0752310564ff8badb390,-0x145b1e2eb5babcb9ffe18843694a9a8699d36f0c1a20158cc91,0xc3a060ec097c6f1ea6ac01bc0803d7076df996feed6b82ed88,-0x6a3ab75796e863070a360598d66f6c582a55c6583307a49ae8,0x3410aba54c240064721f04a62ef05b17a00aa9bca350947018,-0x16fbc8845da9b2ae4418757c3bf34432ad01b5780379ee275c,0x91d36abea2728c442c9eb024a8f2ef5809be9c68b26a730c8,-0x33c80c8d7b1120ceb952233e0e1251d9c23a537c6a4d53838,0x1066d8f6432d1bfcfe2fc05e4e00c051614ba59ae9407ae98,-0x49cf5fdddc5742f3948b67480232ce52f7f1accc26d113ab,0x125564f0057925e0b4b38ec24e6e25d666215130127f4170,-0x3fee6adc5fee76fed3d44ff382cc0d3803cba33bbaecb7c,0xc21b8e56143d578933c4d0018e0977f63df2a27277ef70,-0x1fc692a7612d296ab60a6b4bd4562aa078cbb3ceb5cc8e,0x46ffe06442dd53cd9c4f6a9fc34a3300abf52f03899e0,-0x858002fcadbdb78404f31fd9d5100e0ca56c6db9e2dc,0xcfb532bc90344ce68c2823a483fe3afbfbc606b3b40,-0x105cdc99f2d2e7ddc933b9ef9c9b8308f26a95f6bd7,0x1042d6451c770dcb1a3aa1a52c057e31ebb98c4a68,-0xc4b842783fba07a3ceb5b4ae276f744f946951a0,0x6bd19d7ca284392749f2d932cc832aeef6313f8,-0x28001f7578654b5f0145adff43e52524cb5290,0x910f4d1fb892bf6c576285f8c0cead6460c8,-0x1101f2a0cfbe786459de72c718b612eb910,0xc25ac193869ef659422c8453d30877d8,-0x19a062a007519e10c2aea75235d949]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 25 50 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 50 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 58 indices rho q5 m5 5 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 58 indices rho q5 m5 5 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m6 : List ℤ := raw_ints% [0x0,-0x41b26b0bd71e7b374e43df70a3d9f164767497249000,0x8e3580ad75ee5197d09420bbba6dcfd56bd5105a45c00,-0x95d02b7a656d66d977639ca30bb03435084a38f0c85c00,0x6657871bebf995b181a92181e2f8a17fca6dde765afec00,-0x32f7288b503a7fb95cab1c0621d6a140942b53ae939e6600,0x13b86c2ec1294ca7bf776f7e98e7fca3a1df1cb31f9482ec0,-0x62bc4fd3dadbfb96a1c0378e141af37ba744a591ed530a400,0x19add1eaad87b11f0ffe93f6dfdd087eedda6195d33beabf20,-0x5a94ab909f720d2c62631735a6771808395439f07fac1f3600,0x112e3bb2e963d9ef34f6cb85d9f97c368b36cd27fbd31428f50,-0x2d5f35dbcf8b67cc52a870fa5df0146dbf5706a59b992289f80,0x6936740220d98d1e8d4753b61753906064c9a4edd18f2be15a8,-0xd7c609ac2189bf062c82af15a7d2bc74a5f15fa1548c009e040,0x189a0a1b8caaa8352c06fa080bc4385855023a8e1f1d05bf0c50,-0x281bbb78b40ad07a101e31ec0f53375d7c56400bb370aea36640,0x3aa81be03f960cda676e043181094fb183ae7e7ff8b62aad51c4,-0x4d2ea97cb6b4cc7d07199a4f09849f5e5d7ec522bb50b17b7d20,0x5b97975e0165f80d3b797aa4107d3c973802da40cdbc52013594,-0x623393a67e78c54f5f5f5a5bf115441ad4384df70df1ca192040,0x5f3f81dcf6fd199a7b3e03d65ec6c24199309bee9a8d38c212e6,-0x53a4b8f802e3b03124a554c464d1bd4273e2ad37526bb8b27cd0,0x4287a21dbf8980fd9bcaceeacb0756708b7524a396bd014c97d4,-0x2fede1aeaf0c97e0fe856987af93d525f7e2812fd302a6609350,0x1f42ba679dac29ebf708f9759e000c5bf77bdd25e778f3d22d19,-0x12718ef927659b685febf393a451cf227c98b37987f2bf693a88,0x9d4b8f80b766b73aceea73b376a17f5baff655092fda7e29d50,-0x4b9e5e725954b447dd3783093c7c85d1aae826a9bc4d96a6cd8,0x20b74cddc184c3f30d6def774d0623b5fc45fcd3b492e97da44,-0xcb437912309c96f87cdc5acd6353b2c853d5b9ccc545a2b6c8,0x469c1730e9eb56731ca70d872570577eff7e5a76670b4ff340,-0x15db605c718e4c87a91945e48a873679cd983939049e774858,0x6002c3e88030603df459e5c93605a863482b08cb3b9b25e93,-0x173fac662a8e522d0f3caf0d66c4222f66ec70d5462ed3f70,0x4eebbc33f94ef54b8204c98158f66a566967c6fa05d03554,-0xe8e3bd6f3d3911497f4edd3dd70144fb23a1df11f049bb0,0x24fc9a00ab0025ec1f251464c5d58bae32dbb9780a13ea6,-0x5003294e09428dc1c5cbe5bb0e015b2e09d13301f0c0e0,0x9150a0a5f7e53574711eb82055c32f13c57681a937714,-0xd9c8ae887a5c7d521673c6452859642ff151d3fe2080,0x10794440439a1f9ffbcefd40797072f5305f51fb0fef,-0xfa929e54e28ff1006f42bebe5db0abb41a39b24b68,0xb46bf1a8952b8d7e77ab48967253abc2a1b7a0c78,-0x5da8600683cf2496c73069c5f778af2749f83338,0x20b0940bc644a2c23ab4fec35e50dcc4377df68,-0x6e9a6c2e73cbefafa30797fc9f3bca649bcc8,0xbf908bf1cce3c59df6d2f21592502e86ac8,-0x7caf2e684de9c36672f9539066664a218,0xebe8c9be38b7720df8c03278529ea1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 25 51 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 51 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 58 indices rho q6 m6 6 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 58 indices rho q6 m6 6 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m7 : List ℤ := raw_ints% [0x0,0x877ffcc86baede22116bfcd851f181df345077bb69000,-0x122834ec94511b71e02ab0d72280f17cfe9a771ba2fdc00,0x12f12e7311157844194d803472a5b29e37458c43376b0400,-0xccfc69638e4d1f82ef9a347026dea49d5fe849f2deaf6200,0x650c40b437234c250276f7600f9c482f6444709232f5a5600,-0x26b1d8d556fe3073ca4610a579aaaf984aa36a3b7268188640,0xbfb00ff7438d9ea09e9c4b2a30b3768c3fc695a0e2af41d000,-0x31509f83b6a5b1f9253f0ddee8de92a55635879838e97109ba0,0xac07f39473bb4416f4e4fb076b8f33ac5436cf40ada800b0e00,-0x20429106e13b48bd7161fe296d911b1bf250295be7c81e797230,0x5434ff6de369d850436d90a35b603c35a1fbd388de4740cbd480,-0xc0f25b7e1f6206e2ea08315e7bd11aee345450f3f3da693da448,0x186e0f2cd7e703780b3e4dfc7c98df5fe64abf2961587b7e68e40,-0x2c02588c92dad175da4a196db795dd9288711a775ae36124a3db0,0x46d3ac225c67ce74800556c4458b006d546fd3bcb37f956cd2d40,-0x6636bd19252c0e2b03b07be92e1a7272b5c0c91ce4a57ecc62e64,0x84ab848609f1dce99b2dab577f424df2782b48bf234ad30479520,-0x9b3d25db059345353e5edb69e5c811f40ef9afe43dc0ac18d9dcc,0xa40b449fcab343fe15031810534cd9a84bb816e2d7391bd098980,-0x9cbf4e9d14d8e4cd7bac4eb383c1c5c157ed984c151aaca09540e,0x878a107f8388c2c5a5e5d1a512c107c628acbb75560f04a860250,-0x6a196ffe70248d60c6bf861c066f59b468fc719ae57627f80684c,0x4b2ec09972a68e6999b5a63beb31c46d1686e6240d5de0fc1a810,-0x303402ab72f4fa3bb35539f4949db0be4ce6922d8082615f9f021,0x1bf041dc5067b384448d2a46d2d23100a97b180e2b93ac2d2b888,-0xe9e948cbc63fe8f5bdc80480701fc5123dc004049bd325db0ba8,0x6e4f65a33aa18d9d9df878a323327a41ec3bc3b808c433c46518,-0x2ec7325b280a43dc26bcd3ba71565e602922d5f5ed6cd26f2e8c,0x11c9c2fd50fff7c93757790797d7c86432060ad881dd81616a48,-0x60b9b20ef12fe4f8aca6bcf82c820f2217f1e2eda9558d4f258,0x1d42bfcf83529172ea8851b47d448305f467a91d003f6508418,-0x7d77149e24f9ee313d2bf0c9af1f54cb56675020ed79ebcabb,0x1d9df17d58b8e032a088d7a8894654f2e60bd1d8562af36f70,-0x61de08e949ed43288c36a59440814261008ef73cc7e9bb5fc,0x118aa8b0f5bbcff95c38f3704d2ab678b03f8e8fba54f5370,-0x2b3d3e2b2bfd923404f0d3005c2b5d0bf9917fcd9ec0cc9e,0x5a8bcd9c1e598c72349c627d94f5d5c5297cecb38af6d60,-0x9ecda5385c72da990d6539a43bb3d557f1aec6d41d37fc,0xe531d4b63acd3c5a07fc00eb84a2a84b74ca16b05bac0,-0x10a433c8acdb4618915b39f3614afe7a1e83d4290a007,0xf20ac3b9575f89d206452361e2443ba84a08c01ed68,-0xa5e3a83a093c0691c5d8560e284e75840a51043860,0x51843c64851602879ed1b0259704fe922dcf3acf8,-0x1ac063df0bc5e3c964477693b22b133e695fcd60,0x546485f4a4471f081a00cfd97b263c7b96f948,-0x86e03842234c6141254e01fe121e5d986b70,0x4ff89c7dd6bc064ce89ffc39fe5dd15458,-0x87b2792c6dae97e7e488501768d1039]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 25 52 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 52 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 58 indices rho q7 m7 7 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 58 indices rho q7 m7 7 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1]
def r8 : List ℤ := raw_ints% [-0xa9e39e257a09ca2d6db51000000,-0xe8e8720f6375414ae8a15b80000,-0x98347cd3235f404cce8c4f38000,-0x3f1d3c1bc426510720e1a525000,-0x12a61c83bcffbe93dce721e2c00,-0x42e16209e7910298c75d7c4b00,-0xbd1e08350fcca0d22c8780cc0,-0x1b0a7096bf015d9752fbcff00,-0x32f4b4d588862fc5b6df7430,-0x501b9715f423bc1aaf4e500,-0x6a0548699e811c5d8e99a4,-0x76dcebd2d36698a7cb8d0,-0x7154f9755005d290c74d,-0x5c13b95af8e58c81dd9,-0x3fc013164007b55986,-0x258c1458ca378059a,-0x12bdd378cce8f3eb,-0x7e15244044164e,-0x2c432ecbdf848,-0xccfc30e1510,-0x300e6e8db3,-0x8e496071,-0x13f7cee,-0x1f8ee,-0x1c5]
def m8 : List ℤ := raw_ints% [0x0,-0x11777f95d5e18aa2643eeb97e29021bdc5be5f6f2889000,0x25198bd462220e757ae73df9961b8576c48695a9002b5c00,-0x2655e68ca255981df8f7b44b9092ed252d4e1a743aa195c00,0x19ad30bc7aa578941f3ae6ae6fb4a2903951c76152c99c6c00,-0xc881594c6cc84a7e202142cd17826150f46f489e801cd6b600,0x4c004fcf2b4a29cac3f658f5bb18587b8606f935aa7fb334ac0,-0x17497615aebc684f9b38fd3f0035a07cd1b273c6e04f16543400,0x5ed6721c7e820b28c8ad66a7547b13a811f1573af0ac4f441220,-0x1473cc57734130b0009998a069144e513c33497165aab6619be00,0x3cae8aae210ab7b42666e4278c4668104849e426fc351b29f7550,-0x9c967f26ae9d78edbd6ab5aaa2b4460b91c5badb43cb744e0b780,0x16298e3801b79cf380902bb6c911d9fd0022dd0b42d7255dd92168,-0x2c5bafd08ecaa1a1dc5f01f7329f5a819d9da580f14657392be240,0x4eec66c2c541a9f856b5c551da5ca0c2822162882ccafc554942d0,-0x7d683dab933a84b338e926ec59034b09a70fd8cc986a28ece7a840,0xb29f7caa379c9d770e154c3e2767a1f99f2e06b8a8a61a2d118d04,-0xe4bc98bd502104d1c0fdec79800b1d677ac793f5687bc952fd2920,0x107f31bca751e67a42a95a97ab897715dd854fd6fe8fa10fbb2a994,-0x112f280b299234db75c7c42bfbd750333b6fd70ecfa2f011bb95040,0x102dad2ae79408ca5952e188c9eaef7cc0c44b5e90b385651aae556,-0xdc6e7c10d0b4a232ca1232caec0e1ab5d925ec89b7b4a21d520350,0xa9d7766894ed4c53b6410bc451e54f5ba5c38c76631818e753b2f4,-0x7664998098d71f4c61c655f472621d9b705a1a7d28f7ad8e8349d0,0x4aa08d597debd8d2415fd3b7360b2dc94dfd31af78a72f657e06a9,-0x2a7f1a1870de696003138055943d17cfdbdb6b509db18b0905bd88,0x15d51c08569400d625de76e1655a9b3d6ee68d30cfdf518a8bbb90,-0xa19ce7aa9b15ff47ff535a6157ae037f4a5dc846fcb2fa5a0bfd8,0x432dbb09916e64788b4435bc48058b57c1a44b956a65add80a234,-0x19049cde24bc735c1583508f095cd4bf8f21e04ef35172b40be48,0x8518aa6b41128513e6b5c74c00f377fc908be9832888a5e20a20,-0x27598177005db2d60b34aaa197b05b7b980a8123567ba7e863d8,0xa4b26b6134816bdf399a6f2f16980158a260ea0aebbe8f3bc23,-0x25e634450d1d58a3d0a49303163c1bb56904c0a49ba780b6d70,0x79e6c4d8a56eb0ad101df69b07c804f7f2a324fc9caf06acd4,-0x153b7a724ce0b81becf1c9118df7e35a9d2882187fd60fcdb0,0x32c33cff0d551b06553a0ceee73c3cec4e5f73e215ec72b76,-0x66e222524e648062833cd846ab4fb93d320ffda6898d0660,0xae3655c43284a76ed517c7b5d0c3da951899db576fd23f4,-0xf2115756a786ff01d231c1ad05482408236c296c7d9e00,0x10dd94c327830c3d18e73b1ae889d913ec640daae82d1f,-0xea784feff9dd5b021f4139c59c7f9bf6105051a3b668,0x98e45cccecbe8fee03b0fb6712669febad481bba8b8,-0x4714af756f18a86c0e9689e037cd1348b7c2867638,0x15eb6d25bc26b13d1c5af19a7652d48d141c1a478,-0x406f88aff38b5a0762f5118bf78ab97f0c94748,0x5ef94275f303257b570758c90340f4c5fad68,-0x3347f235769e75f6b8b9db17e6e57307098,0x4e08edd51e17ea31c8eaf1b865cbe411]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 25 54 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 54 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 58 indices rho q8 m8 8 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 58 indices rho q8 m8 8 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x1c5,0x1]
def r9 : List ℤ := raw_ints% [0x12c9fc6d850f352c26321655000000,0x19b796e37158472bf6037d1d980000,0x10c6bf86f8e3417869e95a6d298000,0x6f1686e04ef46e215060bceb41000,0x20c0d33901ac65ea9ec41d5118c00,0x752e70b34af39daf1af9fad28b00,0x14a780e65467c086a5c55ef244c0,0x2f1c5b328aed9dfbf3ab0f72e40,0x587a5cf46ea55caf6769ab99f0,0x8a91870c807ad8e9943e904d0,0xb6999fb186383f13ed6b6a34,0xcbb498c5762d084f344276c,0xc11d8eaf6970cae724e1f1,0x9bd99766a636f3eecbd00,0x6b0da630b8795d5c9145,0x3e74ded001798465984,0x1ed125f0f28870de85,0xcc5d9630e658f870,0x4671916d23ffd5a,0x13e77685d206b4,0x483a7b97b23f,0xcbcb7d9300,0x1a85d21b5,0x24e81dc,0x1a813]
def m9 : List ℤ := raw_ints% [0x0,0x2406772509212deeeec1c5e94349459767d8a4d5439a9000,-0x4bd1edbeeadbc987869b524e837bea0ee42594ac90596dc00,0x4d9d86cd377b08bacac866ae2996793b144d64505011b20400,-0x337d8d1f0554b1480e32202c48cb97e4dffcf9f93e4913a6200,0x18e2b55c70ee694334ba802779b5ddeefba300c843de9ac86600,-0x956c43b19f38751caec6b50c86bb8cdd1e8c952ebb1def321240,0x2d51311ad01ee8f85f60c216a05596bde01151749072616bfa000,-0xb6a1e591c00978bc80bd621b0b076bd558e166bcadb285b6fd2a0,0x26f70fb694c611948b03324e6f73ab3ead8c420302338f85fe7600,-0x7257d7d81ebb8965de68875561381d867da1df4d437bb0c6fbac30,0x123bf2a3949ed594e5de7889a1b650a78e146024fc784e872705c80,-0x28d0e527cf9d90debb2dfebf45abae3e38ea6b0cc040d1d8cc33d08,0x50ba284598a5658ad392009078ca06425049b9292833f2a16184840,-0x8de2e0630c8ab44df93b7a69ea7d1c427b77ba0e13f37ac4227b330,0xdea287cf400872d3d1378643e3c7b66ae7365840045b7a7cfdf8f40,-0x139076b335d15af7b0c64c4c3088b6a2ae5e1c704219983df1eb69a4,0x18b8a191d720fb854ae3c25a515718a893743d2222e186f84a5f9120,-0x1c232360f1fbc2f26f67b9258cafbd7203f01e050a4256095beb55cc,0x1ce58229f9bd58679bb7e4fb86f0fdb29d28488a860821c2f2bfe580,-0x1acf27a05bdbf11fe36d82cc702845c30507a1101ab5321c36ddd8be,0x167c75b0fad90579972926ccf0173299a465450425eeb3f5d710ded0,-0x110e3c9a971be877079f920edb51da52f0472dccac4a5d012355ce2c,0xbb27a3d09bcb9274ff848baf62fd492a8138b7b60a2501190a94690,-0x73fe82b277bdd5dd996fcf5e972d9b09f66f5ac095cd0824d41dbb1,0x40e749ae2c33c78e9290cad8f3859b421072d8106122e64ff0f4f88,-0x20bd7d0d99d28ee233f5df37ef1652d7a4d1e38db0298e66495cc68,0xedc86672c656ad32d19df3c83677cac2ce96b76509ceccf0bae418,-0x60e4b691b434ec06c98bc8fc73182c1a76ae839a55d6c32a31663c,0x2357327bcf025522a4d85a4a24e40dd259724fd7727b6f2eba63c8,-0xb7f3f8c67224c86f97142bf178f53c21dd69ab4ce3d44dc32e978,0x3526e425188ccc04787a01f18390e045e7db424c876c9d5a54798,-0xd92794fc01bd9b711fcd7acc34d50fea0dce1bad1c61e9276acb,0x30b60fd68cfc2817159cf9386d24ffee8fb2ad76a1cc8f0c2570,-0x987f649b1125f33ee9da8b207b7583403da4c7e9e98bd6b987c,0x19cf134768ba8bde3e2a21c59d23df09680432af2c688284970,-0x3bd74d640b6c7ed1fc13e39be7ff31f8e44edcf83384a0e72e,0x755d31fe7b31821624340e8694c85d7b1daeba07b2a71ace0,-0xbfd4ad34ab192042789bb7b527a6c338c15571a0623b701c,0x1008cd152e36145aefc90fc18d7f19a67f41041c0dc19040,-0x112572dec7e894aa72e9dd548613f1b9a8cda570085f237,0xe3c1b1751bada5d6149ec8dd91c23b2e7d4ebc42c4c68,-0x8d3bc3e7192b6e871c666139e028867eb15bacebe720,0x3e16d5bd9581087f2c0f5eb3ad0b2e53dd49fe663f8,-0x11fb42ed832e75a031501cc24abd46161e3439bdb0,0x313a1c3ecd4e94f9fc585cd5ddb625948ce209c8,-0x42e1b62008285c74fdbc8e9cf53d97eee490d0,0x20e049a05a0004c7bb758b45c5224ee4dad8,-0x2cdd46ba61a3c73f81b4c8dc7d7e06029]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 25 56 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 56 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 58 indices rho q9 m9 9 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 58 indices rho q9 m9 9 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x1a813,-0x1c5,0x1]
def r10 : List ℤ := raw_ints% [-0x1196d99d2cee845953f1306f03000000,-0x180a5a6631b8da285277762207a80000,-0xfa86c134bf2bde1e3c6b7fccc7a8000,-0x6780aec10360d0f44b5e949db727000,-0x1e756b076e7fa631e987d48a2693400,-0x6cbe33e71e2995b1919d5ff7600500,-0x131f4dfc7496bdcb117aa1bb346740,-0x2b80d431a243f414294fe326ca840,-0x51774df7ed4887354353fa0df150,-0x7f2bfe794c11f8723a26ce02510,-0xa6f785e28654f069fd2f46125c,-0xb97d1eff96649e65abe694c3c,-0xaf01dcec78e7d89abfedbfcb,-0x8c75a78a7821e4dc4c1ef5a,-0x5fdd4167e27b80815f6af2,-0x3781f0b5c90df10219361,-0x1b247c6b6571d2864965,-0xb20b3a26bc5dd71a48,-0x3c8cb6dead1f416a8,-0x10d1fa581f9eabca,-0x3bb4ab1d0f1f85,-0xa38a8882af76,-0x146ac38e9aa,-0x1ab865931,-0x1172d1b]
def m10 : List ℤ := raw_ints% [0x0,-0x4a4d55bc62d46ebccc6fa8311ac71f88462ed3f7db6ec9000,0x9afb750b85506711f7dd1eb96af5e052942d82a3e9b8725c00,-0x9d344159e00affc1754852e1aa7c961dfd12418ac9fb12a5c00,0x67512904a16645a8d0e445c2f32257f1ec562aa1a51db394ec00,-0x31750565d2dfd72427a2b5753170f9a88fb2487c4eed4cee28600,0x1260f68dc1b0f949417338d8cfef51fbbf21db0721168f3e30c6c0,-0x584a8f08f0ba8e69e113bff93b29e57379065381215ba67a3f8400,0x1602d7ceb424ac6b802c77f03f505d0bed8a074c67dafa618a7bd20,-0x4a5966c6881ad6483d9c4c9bd72223aba49d0aac09625cb34dc0600,0xd7d441914cdc1bd2af0a26a8a73be0eb29374d4ed1b6822b0b3eb50,-0x2209aca2dcea8c714c2928e60ad435a84f5472e7da8c156b00f81f80,0x4b53b9358307e409ea7841bb29d6dab00487846c0e11b78fa985d328,-0x933f645b387f450d4d98c8193094ec81b853509f960166e69c367440,0xffb36720748dad7de0b019725115156fe212e9cbf0b73db262148550,-0x18c4617f8ac4a7e70592d8c44ba8f337ef2e1175f2a629050fd01ea40,0x22617834c9830c4d86a3edcdd5d97b8b480cc68927c6c7fbcbb4f0844,-0x2adfd4f0bdd89c775b65beda5bc0275e24a49d8ef5d29bbaf8e5bc520,0x3023ca5fb7788d8465f2c32298d7dda2066c49beee9edb3c21daf8d94,-0x30bfd8d4b25a944c2ebf3bb08beab7c60c59bf91bf78327649e5e5440,0x2c937e0c50d066e808b015f630e0f605275129b806bfad799760cc346,-0x24d4a1843f38dabc7aca8887abd0c39c910827131747834df26719dd0,0x1b81141d69fcfb90841cb92b267442436acb6635ef47a74e4a945ed14,-0x128f96c864dc8ee36d0243b14b193ef08b08b76ce1d9c86f5a0a20050,0xb4fee223b1a42270fa72b0543666e447c787e0417aed841f72ddfc39,-0x6385bd55cf6bb549e60b35e8dcfaf8419b0af1ff0d19c3affc9eac88,0x314c8f9f423a944e771a6f8252b2d0dd7039def37ec875b576475dd0,-0x15f5128f1305ef05d636dd2533049dc92653dd234824a917c47f5ad8,0x8c58a6795351f3cc6b08b0fe6c8a806799e11c79a765d65cd2958a4,-0x3223296dd8536f95c85f1cbbd01ba60d292496542694ce80a828dc8,0xff588243c9a33304267de5749d283ea117ee79b94ccd5537c08000,-0x481bafc6f9b99c0e4dbc389fb5de8f599819eb8dfcd28ddc6b7b58,0x11f90a9df79eeb80ad2dad910184b8f72f39a57f1360aedb9822b3,-0x3ee0a9709325baa8989b6397e8dbe7027931a81240a0597382370,0xbf95829b7ee8672ba71a7a582b7219689636d913e5cfc07d6454,-0x1f809318cd04b43a482d7b90f1861fa736eeee471c14f59f43b0,0x46d3a46a0eea7dee043ce4d3770aa68f6fde071364afc7da8c6,-0x8665e75dc5b4656c7d85214845a1d414c1d22743ef6f2aafe0,0xd3ff3b6e5025095a9d31f2ffdf77d197393d7cacd079d3dd4,-0x110cf57595b53546791c73b90d1232864ac7ee928cde93380,0x117bfa005af04a22795f8c18188ad29fa2c09bcc689c2c4f,-0xddd0b292cf262e1b22a3ba45ce3e20faefaeb1ccfd3d68,0x82bee2cefa1b7964bce5a527b0263c9f23e6e255ca0f8,-0x3652f0167992569d4e1647fe3bb8b54a69ad65f14938,0xec44ed89e042a614b7370fc6b74361b54048afe908,-0x25a0b20410ce709842bd9931847c97282740fc1c8,0x2f19ebd4807ff59f9976c9b7390096805447908,-0x1512669ea1de41112e0e1fea9c29c10772b18,0x19c9a14a31790fd71ec6924335bbd3da81]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 25 58 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 58 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 58 indices rho q10 m10 10 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 58 indices rho q10 m10 10 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x1172d1b,0x1a813,-0x1c5,0x1]
def r11 : List ℤ := raw_ints% [0xb9450048a64512ef14df67d5e8b000000,0xfce4f0218351fcfce6569297a9f680000,0xa47b5fab32b8bdea893bdb66a0b868000,0x43d9748cb43efedcef66079d5a243f000,0x13eed18f5a2175c5aa8bf446d6f783400,0x470813d4558bcf5b22cf8da2cfe1b500,0xc77129ecfe86c98ccf55d5e2cc71340,0x1c4b2f8467408a85d2d15186f8d7dc0,0x34d99e35364183cbc48388fee108d0,0x5244ba15e609a49c3120e1e8ff5b0,0x6babb01fd031990ad4359b37733c,0x77303e035cee3e28b4d5c4ca294,0x6fffc1d2b0c672883c7fc7a263,0x59799a6107b9fa0a6ed0d65c8,0x3cbe35d13a93b464b3e6aac8,0x22f473abcc23693a8048fc4,0x10f80fc68e46fb0b197320,0x6e5ac56b951836000760,0x252452015faf985d910,0xa2fe748792c8384dc,0x2396a74e746bd987,0x5f8183588ef5e8,0xb9ad05d442a4,0xea2450ed4c,0x9101272e]
def m11 : List ℤ := raw_ints% [0x0,0x993f80d48bd6246565a64ae5473ab10910c0952f34947e9000,-0x13cdb96cb44cc0369f3b1994d6427b9d20cdddd72120c6bddc00,0x13e875c9b6d1d268f84e39c7aa77dafb755f75a4e37f594390400,-0xcf6dc7337a62487287a179ff5b6698b3a2a5b2216d71414cd6200,0x625daab441b8306263b90376b727918d454cdaa21efd3470f8f600,-0x2434227bfee383a0086bc06f8dd07d2f19c90c20693cb47cc1c7e40,0xac3713d84e5b96a00a839c4210b85fba18d7601c778476a40577000,-0x2a8069e6e5379b2454b7a7849d007183cced3fafbe4fed7f8f8681a0,0x8e14d0426a144c01e0c9e636d5cd19c61a215b33ef1d4dde741d9e00,-0x1981550d595dfb77896e83958f18a0f7fd8bdfd7b7986f9fe86139630,0x3fa878661724bac1f3d4cd445d17a625f85994b7fa36b5b0246b58480,-0x8b4df72188d82b0b9bcb9fb0f5a08d8961e314718179f732ff263e3c8,0x10d2ea6cd597324099c1b85a5441a24895014717b91e5b38bd21e49240,-0x1cdebc981db7062cdb0c170719af437089068c3feda4f853260bed1cb0,0x2c3277bf80fb2a7d0f2b0a75a1f48b31254ca2439e32b3f9eef6db6140,-0x3c9559298633e8c1c6285d80c3061fea0266fac0a0a47772be41b9b4e4,0x4a92b478e3b9e8b8cecfcecd10ecb0a1ba7c871afa58609152a5f07d20,-0x529d0c15fb310ba9fa7c282c3302245b9992765c9577502c7415f0adcc,0x52815a80922a36ba3387ec6531e9ca66fce46584f0dd330efd3c848980,-0x4a5d9713b0e6b038d7d08926680dcd4cc043a1d75926d6f49925b14aee,0x3c8927f91f91eadb4179a333f2a939d7dec99902ed144e86e43f168f50,-0x2c839b705c15b1698c07a2c043213cef2061a14f8edb5e50f16769d50c,0x1d8fe7bd1883739486f994e8c7a7c2162fe8119bc0b4c3263ac1fa1110,-0x11b8273347e0511780bdd0dfd12f2a9862d3adf6b147b7a444cc96f741,0x9935a8d6916a9e130f79ace20c0ceb1a4473111973f2838ded2045288,-0x4a88687d654758dccd6cd311800f59e0bebec23a68d8f57b75459bd28,0x20932e57548b862adaa2b460aa03e5b3c4e8ddfa30f49108b5b809f18,-0xcc22fac05df416e8cdfe57d3ec8f2d6745d9577737780bcb0fb8526c,0x476e2daf42f96412b1e6c0fb3258165892661e943cfeb998b58fa548,-0x163f5109f0480f21a49d41063cc281ea0f8e088857c3006ba73d6598,0x623e395d6d7233513a30424e9d257255760c38cc8b07aace1a61318,-0x17e6daa8c646f4236f45d11ebdb94f080f2bfe54429ad355590b3db,0x5181ba2bac57b6b4a688841ef2566d280891bd89ec04dc8e166370,-0xf1b068e9a7d27a61013c5d8cae82580c033faed974f10ec8872fc,0x269b87e426e605ecbc8a3d6e2d2c372093a53db8045bf3b80bf70,-0x5428684b1a2ee0dc3551e1f9187e8f8610e093a7aa19a8fd403e,0x9a7aef62162e2ae26ed61fbf6d4bd5449d85dca133033411060,-0xeb1b5dd63bdb0d1315e5366ef5c7ff4f6bcdaa19d7e559633c,0x1230a20486e93bb0dbef339869a6d6c9b5174d4590dac521c0,-0x11e174e3c7319620a7659d9a40448309eec705db1890dea67,0xd891faec9e999c319023bfac7b3b79b4e8cf9c1ba61c768,-0x7948e3080ef4a513c9c5e0b106ba04af2d6c06eb8e7de0,0x2f9a63bbbc6311c6c5e63171ca972d4e58e5dd152b6f8,-0xc2392c9d9a3abdd4d500f1c60e50f7b43b73d192f80,0x1cc66235ffbd5bab7bce4480e57efbe6a302720a48,-0x212bef2442d76a7610f93988d34658264c22a130,0xd80b764006a83f044c3db83e3f78d51e0c158,-0xed1acde86f8f6383822cccd812c6f93919]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 25 60 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 60 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 58 indices rho q11 m11 11 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 58 indices rho q11 m11 11 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r12 : List ℤ := raw_ints% [-0x603ab0770c4325e0f0e03ba55bf8e000000,-0x8333702823e35f487bfd92f367864100000,-0x553985434acb5d21a24d321cecd5cd90000,-0x231b5c72166bc72c855858da7c38973e000,-0xa4c5232d60d8a698dc02649dafa3dbf800,-0x24a3088c630012bbe44fb9529a974a4600,-0x66ae5b785f74c8defd22de2d84c61d580,-0xe8997c958cf306a0e497cc223107bec0,-0x1b182235d03a8717c890e6f91b7cb2e0,-0x2a12630e4bf39798db5f4f3aa229d30,-0x36e92ca197cb4092d5ffe438ed41c8,-0x3c98ef9e5c2c81d3fd033c63c9824,-0x38bea01885438be8657239ffdd42,-0x2d279a0aa25121a204e979cf67b,-0x1e847aab5715ef2d410956484c,-0x11789f74786d59efdea971894,-0x86e53295a68dba5cb2a2fa6,-0x36727b4d1bf297d99dc472,-0x122c94ce89686a2d38b10,-0x4ef78d239838c8dc398,-0x1108b6b0bc77f51cae,-0x2d0755f279dbfb9b,-0x55e0bdb1bcb4dc,-0x699cad223338,-0x3f3b0c6c0a]
def m12 : List ℤ := raw_ints% [0x0,-0x13c12f9b66069ab1121a6fa78e2e90d22b28d33b15c724509000,0x287eed1ca419124b44f91600d8dab2590b10998bb45399e795c00,-0x285a74b0b897445104014b542c1262e607130a54f42b4015fb5c00,0x1a0b1104d9d59dff3acf09abea1117aec35bde9a4b998367f7d6c00,-0xc3ca414a63867e6345f65298c872aaf3e23019496472be8857cd600,0x476245d7a86dc265398c859364f69c35bf42150a1973436ca687a2c0,-0x1504ae74b519a8b83579242030ce7fb143520869489f05ef31d545400,0x522cde7421a44bb342d4ecd6735a16064c4ea392b674ee299134c8020,-0x10fecb4d26ba54c5210d9677b73dcfa7780c5a2d2989cd355b75930e00,0x304e36af0f229a1cdec9fb8871f8557094b0f30dd4c9f51391b75d7150,-0x77469733aa239fc6f687c532539fea63b809227fb27bfc0ac006248780,0x10224da82a38fbc46a9b7b688e162c1b4625ddf1c8188dcf6b79b39dae8,-0x1ed2ceabb5377d528181422527307efaa782a9afdf992cf1866e8a9d640,0x3447018c69b45ba21ca3f286db7470b90c3f42a0f256a9aa73d822af3d0,-0x4f121212da822444fdfaefb0585a262540b5cf5783bebfe77a30772fc40,0x6b0b5e9b8a85fc9f07ccff5fc169757d8244cf8e9ec524dc1293e206384,-0x821430390fdec65fbc73bf95f51335f600e186071662148c5b7f2f05120,0x8e33889e46e2f8b76be3c238275c19aef8a9849ba53520dc12b5bbc6194,-0x8c137eb586877117cad5ffa8327803873b5e57e344be155200f2c063840,0x7c78e638749829451151f60cd1722f8b3cb91ed256c9dd4e84a79bac8b6,-0x63d70c2b18b49e0348e442645b89fcb2faa1c45ce69ae49461fa9d4dc50,0x484ce0878b93a74cfa202eff6d32602305bc6f21c92d5f0650d7458ee34,-0x2f41da5db5ed168f639cea8de9d5ff86f86b6c96424b53fd4aee74adad0,0x1bdc51295d919f0e716839e04bfab44167c436069c638a6480ddce135c9,-0xecc6a1085b91aad62ab2ac31b264902c3f8d164b9e3a2efe863e6bc788,0x7121832912ef7f7ae58a4ad007b3a321186ca390b374112bdadc77e410,-0x3085cefd330a40b44a0ce23c93c1ea51736ca87e88a3fcb6cb13b289d8,0x12a249d26c5837f8309778e6e11ef2765b5618bf195de4c7fb805f4194,-0x66309a39097768bf7339b427e2dc81005166be04ba5f7651a161a3548,0x1f24a348027e51af43524de7bc1d3ee4e20ba8c18431bfd657f71fce0,-0x866968d6e22dbc15d2f4bc9101d96817a34ed455672cb908969a12d8,0x1feb5ee770bcb49efd2b871e2ab26623496c7c1af80ac6e441275243,-0x6a17a2fa211508d8b458d02cea31d49b760020bc906004c5d736170,0x132234054cf6bd4ab03e60bb2f89f84bd1b0f742699684eea2e5bd4,-0x2f80bbad31ac1885e48a7343750ca0e5f540f182baf1fff46841b0,0x6461529ac48871fffa5ac065b8f1aca67bf3f8758cd7ffa6e5a96,-0xb2357d9cc599a0666b5ed60f585122763497e12be102286b6d60,0x1059fe24052e80c57f316f396cc3ecf7b5b678c322da1fc63cb4,-0x1377547e7b4fbfaf5304b86887a323a4cdab57fcbf34bafad00,0x12564c365638b0c1699aff2c1a584846c7906b998437f4557f,-0xd3f4a56efcda115da728a1168935c945750e8547d7132068,0x70ba1a2e501b54ecd7192ffd9a1c239d3a46cbf20f19538,-0x29c61c6091705c18c0c3162e9e434382f814fe1a756038,0x9fce6462054cd7a4b9f1ff72ba3b888d851100417918,-0x1603956ae1b8b464c10f80ef828cc73eca6f1f89c48,0x175c83bb1dcaf268b09033483b9d2b22b2103e5a8,-0x8a6879d0e9e9bc3450fb46db1640ce7c2dcd98,0x8839184a2ceeb9bea09f9c4bc0f702271f1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 25 62 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 62 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 58 indices rho q12 m12 12 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 58 indices rho q12 m12 12 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r13 : List ℤ := raw_ints% [0x29f6339f09bee6b82ed7a5df3b6bd2a000000,0x3926b240cc7b6f8da8fc15879296eeb300000,0x2514d2c3442a500312a096dacd7a007730000,0xf4187126dfea4a9edb9d229c7d26241e2000,0x47812d833edc49d0120c4708fbffb649d800,0xfe01f2da52ed64579c1dda3f1a6f6a2f600,0x2c6bd295655f1e035f9c5161124bbc73980,0x64720117a1cdf8278bb96b988040942080,0xbad5fe29df6653443dc3524cdbaf70b20,0x1217c249f5fa3fb2751fd76688aaebf20,0x178e9afdc75dc99626a1518a775d7338,0x19ed35eda706580df502bb03da3a858,0x18347e7f46f1f40cf537e2acae4bde,0x13322d9f5b9aefbf8709151ea47d8,0xcec7f6e1f600480b85cfb281ac1,0x75dda72484d4b3c68b384aaec8,0x3897fbc3c8614026f7f8ab12a,0x16b5f5d270ba4202bb421090,0x78796b44d045480abd66de,0x2074cf1bd9b7c762eb8e8,0x6ef434f7594bce00486,0x121eafe8f5c98c8838,0x2210c8833c3eafb1,0x29241e786339b8,0x180f6b575d4a]
def m13 : List ℤ := raw_ints% [0x0,0x28be7230826d9f0d3556864995400ab1790433a9dceabae629000,-0x52d30663f2e9417077601fdd7d2636a195a23cb023ec6d6da4dc00,0x51d3994a50360d4d9fcadd3d4b8380f1e0379835e7931aa2f000400,-0x3458a514bba4c8c2f815244322d001a9aae935d85e07e6da6e206200,0x185ff933c83e5baf2437669cb8686db285d1ef29aa0a48e4ede820600,-0x8ce1acf39f7085284245bb40a094917ae4132b8fca2b108ca5f1eca40,0x2916de23ae241c1fd6fdc09bc49675ce6bba2224c5985f8159c059c000,-0x9f16e6fc53bfbf8d73c46238141539c7633397268ef51a52f4873e68a0,0x20932b2623917a7b51082960b529b22663799e2b678f7b00add47148600,-0x5ba3ce5410d6cd1ab012af00e7a155370095570e1c98073b1cd0a8fb030,0xdfe564e2f1b6c697559a7df70e6c177a571040388afe2541ce8cf78ec80,-0x1df52ff9d6570d68fa5e89f1e6ad475e5ddb9c57b15200a6f9a9d52f0888,0x38986ae0c6ebef612673dfdca030188e51035d25cc802ccd8a7d9ea06c40,-0x5ee27ef51d966b261a2e572725801462c00611dab8449a91d57fc025da30,0x8dd0bc31c08fc3ec0dc8756138398d3a752b605f7428b9d65842b9e6c340,-0xbda3f5532d84bba4917b6d7028279846ffb619c7a0ecede90247d3bb3024,0xe389e518092a50a36655b8230b046aa61b06c01d67b0ef31e9ad95ced920,-0xf57f123a42ca48a4ab556e8538157395583a3ed7c612270146e06b2ca5cc,0xee8f6c6f601bc467d58d27ed89dfb598996f783c11500f76edc2ccc5dd80,-0xd104bb5be4ff90a6e31517627c9a0b52552168a067855dcbc38cc169f69e,0xa538a7f0628da2906fb4e80abf9248b5ca9d2c4ddc2dbacff74f902ad3d0,-0x75d7eaff923e0bbdd7313f2fff3edf742a390ac2130275392bb2e453b4ec,0x4bd17b7d6871a67bccaf72cf2fd9dd168d62111772413f66b2c296e16f90,-0x2bf83af5c681c84746f1d3ebd55addcdaea671d6acd69fda388bcb294ad1,0x16f532733c9c693439dcc4cd4e6d84eda616d086ca9340c0729f6c706188,-0xac63f0c269fbee896c38b4b90a0d021a2d30820597d9d7aa2810ee6dde8,0x489102777d3464bb9318ee071d03a95e0ad66dd6f6426655fbd6a873e18,-0x1b533ed0070f81181e653faa7b2699e466783d907eff006dd68e94f871c,0x92cb002cb25030fd1672a844960f88bc004baeffa79b1cb06b75ff4ec8,-0x2bc67a0efa82ed9ea126ad67a0442cf6e298a7d96ac266b25d03ca7eb8,0xb8a73842203f4dc82a7c4f3dfdc1e880c9866da1770a931534c6dce98,-0x2acd17917623e60277e663ef8fc33d2d9ea0dc052c60c099815a7a5eb,0x8aa73ca069dda8da9082c14a1d3f30afa71c0728334eb2824e78e970,-0x185504eeb10ca8863cd69d43cb5be8db36825735d5562ae53691857c,0x3aac79a11f80120a2480259a308aeb18d3b9c39b7659f033d9aad70,-0x782cd564b031fb6fa8d7356176d682158c134044619e3c4e874bce,0xce4f287b98eb03490a5f76fb7f11fab9736544b7f617f3c6997e0,-0x12418289c403bdd0a6e4fe967ed462eb07c00ff55c9d0d9f9f95c,0x14e50af3de77b5cc338e1ccf65d914337ef8343ee3c5ea5c6740,-0x12db061bb29ec84532998359f545deba45f59868df94219b097,0xcfe9e712719db745341ea062ba1e7fe5ef16de0a7b02e7e68,-0x68f73c65ce7e08bd5b6a9ff397bd81397d0f9b91ed483ca0,0x24b53c7055496631517bfa74eb91b79f989e1885a20fdf8,-0x83993d5f9f104cad4a271a82ddb1f20ccf6f4a25bded0,0x10d8ffbae63adc295e4b902e9dbe9bfbc3137a2c1ac8,-0x1073b5335b28a97642409349f1f7deede5a5d70490,0x58a644725c369f9a4c1a265bf8cb1c887d21fd8,-0x4e3f13d5d0cf7c17712047d01fd1d35a0b09]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 25 64 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 64 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 58 indices rho q13 m13 13 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 58 indices rho q13 m13 13 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r14 : List ℤ := raw_ints% [-0xff79265e5004684fff1eeadd834ed26a000000,-0x15b9dbc524bb09847fbbc2b01383098f5300000,-0xe14efe6bc5d413b08550de3b0bd6a6f8b30000,-0x5c975fd1eced13c8a9996caca1496cab682000,-0x1b170b2be2c8b5996c0fea390358a0c2969800,-0x601a7432ffcf85ee7ecc0f65bb82df3e2d600,-0x10c832e0b1d1b9f954b799c608a9b2df27980,-0x25e2faebccdd3b872d19f6fc85e2627d7c80,-0x46590a730fe1b6e82130655e4665588e560,-0x6cc93609e04f4c561463db6a88e1d2a6e0,-0x8d56568e95f1269ea5259c6fedd1f1e48,-0x9b2f5349fac0ccce8f4ca5bce0ebbae8,-0x907f783f461f680f8f12616e1566bea,-0x7241d3c1a0076034c63cf8666b6c7c,-0x4cab5ec488770ceecb201820590e4,-0x2b89ce502cc01fd0d6c6d9ba9ed3,-0x14d0f27671ca4571863d6d7a2b6,-0x85013cbc96d793a9f972225cc,-0x2bd979e828292b2edb3204c0,-0xbbc6b1a3cf80ffa8a29c1a,-0x27cfc07c4f76d7e9062f6,-0x67125861e9c125b4d20,-0xbfa08117b11f1ac94,-0xe4460fbd995f163,-0x83380a9c7170a]
def m14 : List ℤ := raw_ints% [0x0,-0x5408cb840d02180b3e0274f7c3d4160e0998aa8e57a4217ab49000,0xa96db7dfe5ec2e62687306b04de51e41223e9d2b4a17a1b22405c00,-0xa5fc574c0e06a2ecd036da92ccce5d6b8681168e22939573e88c5c00,0x6945fb18aa7e9226201d974a2c26f167d445000c28b6e1f16a2e5ec00,-0x3096bdb35b2ca7aa2a49045a9ce409978ab092fbc2ba0fe1bba9b5a600,0x1164c132d02870a10b9b6db912da193969d69b65c909110ab4ab54adec0,-0x506a60ac16c9dc86d7e6119ffa066d617654f9bfaa615f4cf75d09da400,0x134638e59c3b98f8725d9ccf8cb1878c2c9122812ceb884f0f46e8c51b20,-0x3e870a0820bde750b98045f40db62c61dba39f958ed1483277b005b8d600,0xae222b8b16239b5c9da29146f0d1a5f76d92f73562e439e38b1bb7078750,-0x1a50ae97379eece9e8f1ec89b697f9020b545bf16918d1f1ec7e0501aaf80,0x37bc6c7bd04cffd56c29c67684913692a7338b103c44aefa2c4c64b83e8a8,-0x68238733632230a881d9509627b4c981dda0825c40808e636f34d22eb8840,0xac9dd74e36a36f78865f756624a13720dc92d1fbc39ce151159e2df462e50,-0xfefaaefa62262c38225903057c1f3359eea46e49dbb41b814adfc1f089e40,0x150da23ccc7fe10803048c0e60c4a2992a6208f400617a1b8326fea3f53ec4,-0x18f2081f8948c3ee3b707987a0033deb2531a034f8c49dbb17a358c6cd4d20,0x1a911547d3df29e2d46157d7fec46227dfbb7eb3fdf60be2aa15ca0c8ba594,-0x197890664426a0250fc5f707d0b7524bf1fe0e0f4d0f219d6cfd6ab822ac40,0x1601e64907ef9156e8b131bc3ae0b3ff8c4411b6568ebdece390e88f8451a6,-0x11254e70c91462cd6733fa992cf219df48cab504f4f650ea62510408b09ed0,0xc0bd75e838e8af8307ed74b8c24c2df9dc389b115353f6c91dbe9ecfebe54,-0x7a13756412097a5b676c3857e0277fe7da837472a9cc073d0a78b0e8c8950,0x45a5feea86f4bc98a1ef4bebe5220009470487c60e6196258f664dc251b59,-0x23c013fef51dbdc4a79d332770fef301dac663cfe62572ab6e7ae28e62e88,0x107b44d970b946b09825730b76f17bef4fe7358e3b688232763362cfe2e50,-0x6cf354777129441585b24009417d60b61ca182a9d5c9a88919ebf1f2dcd8,0x283ad1da70e24cb224463b6ac7797d32bf896ae55aa7bd495a0f0721a104,-0xd3b649588b7f9248a06e255e5c3ed63a5d36aa6ca13331892a9818374c8,0x3dc7ac837490d21e4e46ab9e0ea30cd436ee052fbe0b5430fca6b8f08c0,-0xfeb304aa4a4aabf22bd68b3a28c7ccb19eaa3377e0ebc2963190c9fa58,0x399f848b3237e4202cb13fcc98a5e60da45d90786bc9670c475fd38ad3,-0xb5ed255530b1d29abd690383c150c7c77d2d1c2b6b563eeeb833fe770,0x1f10346ee5432a178b02b2a57c29f00e0b167d80b6a88fa1581b19354,-0x48bec10a5125bc8ebbc76507f83d0fd1b79daeb7b571c8bededa17b0,0x90652eda0be6316d060b0c27692fbb1eb2dfb6bcae9845df2df24e6,-0xefa91fc1c20728cf9f1379ca096343c46864105b320ff0cfad9ee0,0x14727dbbcaee3e6462954ceeba424fc1db93957b5c75dc75ceb894,-0x167e4fe5c7a1e7d2ce87f6148db354c2eb316e0625b0f7e17da80,0x13704612653145c7edc9451e99f0caff2ebfeadae5f4dc1f30af,-0xcc64c38d3c13dabf2027d0768a8fae26c37ea622de439eff68,0x61e8b185c003aeaf89b7dd8ec2201753ff80397341e4ea578,-0x204c0bd88a89d89e3dcde759c3e5bb0a7ba942e2acfa6b38,0x6c74122939eaa705bef7e29f5d40f01e5ff8380d19a0a8,-0xce5d55117328d5a4368c50780fe3ab5d0f57c8bd56c8,0xb95e6bb55b834347d6bb51e3a61fe8ab50a8652b48,-0x38c4135b995b74b30052ebf418258aa7bb9a4818,0x2cef54b016127c3db44a1108825f275809a61]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 25 66 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 66 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 58 indices rho q14 m14 14 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 58 indices rho q14 m14 14 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r15 : List ℤ := raw_ints% [0x5714aac27bcfc0c6370bc3900c9f0fd82a000000,0x766275b7de41ea86765af037a0a7448df7300000,0x4ca88fee174c3b60fa11e918e49692f91cd30000,0x1f7877c6a5ce121e88ad14c03946af0fa3b42000,0x9327e53b73555f72ce4d157e5b34d64b3b99800,0x2096888b724c5a760ff9839e597c1b05c015600,0x5aee1d588120ba993a21efc9a8a0ed5332e980,0xccfbfd6a858600e1863dc9eebdb83e3587c80,0x17c0307ec987ac42ec59faa566eabd6fd5d60,0x24aa17041ff3ee659a14f13b430594598ca0,0x2f8b563a44390421eaadf006ba22c05f588,0x3417ac84d36e9507ff96801084b87bbbd8,0x306455bb8db322ae357f5abafee4a181a,0x262a48772f2becf462af4e980e115c30,0x19892130ee32f4884470adad5ad26c0,0xe7430b019eb69fa8a4d4df9893c30,0x6e2a09f6f8112f6adb0c87b75beb,0x2bcf79167a2ccf62978d8c1d280,0xe5ffe3a2eec5309302850dd84,0x3d388b4b4510a897091a8338,0xce5b10dd4e78177e992d04,0x21242e86f8843fc3e9ef0,0x3d11665a1abe55d582c,0x47f7d8a926fa45800,0x28d3de053b44e1f]
def m15 : List ℤ := raw_ints% [0x0,0xad5223c05ad451972fe5113f03e56d7cf3cadfc594c2850d1469000,-0x15aa740a14c0d4e7fdbe6c7ba9835298e11e1242948d0bd7f6a4bdc00,0x150d3a0823f385bf62f68e37938329b1a02d5c8f921e97e5e852070400,-0xd3d4c311b724ea41d84cbda29078e3646e77eee8e3e7323697a4136200,0x60ed73ff70e022a6b6dbc91acfbad4e6e60ebec6b1e2ecf0706b44f9600,-0x2263f8c349a334ab10ca3a3fb58f4477886103658b78f9b661bbf04ff640,0x9d8d47e2c0dd5cf1abe4165874d776c043567abdde9ab16a9669f64c9000,-0x2568e967c77f3d69eb60e2d5386a4ad90bd3251acf2fe779d944e338347a0,0x7831ce05b94510b9ade467984e2cf4a36abdcdd06ddb1fcae68503b712e00,-0x14b6be88e81d0ccfa8d184a69141912da980925f2d428c605ebb071a767a30,0x31932209732e06602af0b1fae823d7ddc932ad5a1bf5f5de5bb905667f1480,-0x67e616edcf5a1906f90c3ec801a97dbd1f91824de31c683d20c0c9b00c9b48,0xc0070f4a57c967b41890eb0d7e20fbeb97429fae194666a6f3967a4efa5640,-0x13abeab2ab7b5ddc359494a0716fadaab59c6c63cebdbf1c70f80a251714bb0,0x1cb902d08d999643345d064f99359c1ebdfbdbf4d78097bf492de93dcdeb540,-0x257e48d032c2a6a86ed5775557c4549ffecc572f492a0344dd1b44cc606fb64,0x2be08caee5710caa9363a34519ca46f53b577e70d2eb0f0a1dbe08a748b2520,-0x2e21e21e3430c379e8a3ad157d03989f6b359eecc72623e7238e1621f0c3dcc,0x2ba4f11e4669678232c49bbdd32c463c78f878d966eb79f4385c7c69f510180,-0x25311871a8366284473e0824889f7e1ade7428b2cedfb29c3b23dfc4ff4c7ce,0x1c8ff807acf5a7667835d984a296a5e21f7a8f5eb26634b8acae439e11acc50,-0x13c508798a89803c4610494b9707c74417760932b00e3e62f1634f98139a5cc,0xc53fd0823093b339665530e5ed2c71eebdab6776b6dc3c097c7e748e43a210,-0x6eb963dab5b2fbe09c0f577d27bbcd7a643f9257af595ae4e367eb734e1e61,0x37e0cc4891aee67e0e6beffb1fea6c115b0f79031b08e41111a0858a701c88,-0x194eb5668fa58a3db13f91f7e44e7a2436086ef9c87f55dd0cbe49cde6aea8,0xa435a8e76fc29a38cbcaa014c2480c100c5d6c00c7b6ffc2e0a7390d4c118,-0x3b75f326c4e915fe00b55aa06bd5c967b50f3d786df1c6d504c9c1ccaf84c,0x1328c795202549132d5c2b3c4cedebc79a10adf99e5b1024c095f91dce048,-0x57893d83e506cccd133f24d86f0fa72fb05c830a466d583287b73faeccd8,0x160b5bc42787e678af75fc280f420e6a21e03bcf540946baf792a3725a18,-0x4de22a4254fd7298f97166237c53dc36160df9e50fb36b9ad0389cfc0fb,0xefa1cbeed8cc0453a94cd35657d08349bd8cf03d252a2d28e5793d7770,-0x27cead4de799d9bdddc131e8d3a08299c30b472b93ae26718411670ffc,0x5a86035c391122db61f4a3ce62fa03cb9f78ff71bab8cd3692ae63370,-0xae1bf6085c44c9a28b0ac80fd93ca88b9ffbd8cabf80766b47a3ddde,0x117550fddf9beb118c6b19183d3abaa0268cd4a2dd10d16727896360,-0x16f8f5e64cef2d82da7f0072295edce54c827e0624460789d101a7c,0x18484cc15bcc9175c3027a1034edbe70626d3d4cc81ab0e0e060c0,-0x1416cd2f1134d7ee4abbbaf23feffdf4ca66b0f9ce9bd05edacc7,0xc959cd96f59b1f34002d36714c82221d18ea828a7fda10f9168,-0x5b7a06afc466e58aee721257668812b788b3a1b1690aa4e360,0x1c731904829452f999278286c75ef8260f3ac53c4bb3778f8,-0x597116e0b5261402e61af923d58c0b01552358e6a88a7a0,0x9e0689ddb6512551aa217e9b3d5329aaaa8646a74fb48,-0x8287577234cfa617c3a383187df81736f709834a2f0,0x245747ac68ec8e22100146b6ba12dee296ab4d658,-0x19cca877e3a97bccdd51c0d509545d182e45f9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 25 68 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 68 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 58 indices rho q15 m15 15 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 58 indices rho q15 m15 15 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r16 : List ℤ := raw_ints% [-0x1b182aa80fe0e0119491ee5988a2a6cb3ccf000000,-0x24cdfebbfd1d4c3adcf609c23ac63212de87480000,-0x17cfc84ec8315d7a67e39cda31c871e55a134c8000,-0x9c424a997c054f8cedebdced9d4b0ba916784b000,-0x2d9eb12bdc1081ef2751ea40503d739304f5b3400,-0xa176930efcca10bf3d0b63013d4798f1392d7d00,-0x1c1fcc843f8c34a5dfc05e5a54293725b56ab540,-0x3f514889cb01f304674c2271740605f5661f780,-0x7536c263e33c84582972fd1dd64cee98dd3550,-0xb4a98ca98c03b134a72adf3bdb08561d21da0,-0xe9df02dad44527452ae31f2d1372e5e9563c,-0xffc2ea1addf1654159fb3db58fe4a0d06a8,-0xed19785a435ccd582d76aa97d7324262fb,-0xba903b74086c63e4180c75ec510c73a1d,-0x7c8210da13eac410961ac042c9dbee0a,-0x464641fda6c088ae880d81054403bfe,-0x215e8b65276c7bebf51d5884e53f9d,-0xd3905dc4a3ffc0d59c6c47645256,-0x45229aca99b268b573024dac6f8,-0x125116ada39440657828e98530,-0x3d68e74a3d6febb7e034cd25,-0x9cd290b8486f8d9b093fc5,-0x11ede420f924ea186e8e2,-0x14f2840ba39b3f909d2,-0xbc2a5a79391fdd93]
def m16 : List ℤ := raw_ints% [0x0,-0x1657969bcbb55e847d2c87391f80931d1b6d26d8782d1326afa189000,0x2c562e013b087cf917e7f0fcec906dc047b605a95262e86d6cb3c75c00,-0x2abc0caf40c2089a0a9caa1002bd5107c4c787ac28b7a373fe638dd5c00,0x1aa7a35d8d865d92ee8caecdfa8a962860ecdad5e3e6acc1fc79d40e6c00,-0xc17ed1e6dcdb470d60853c86e5c137b3b472117ef06df0f0ec1e3590f600,0x440eced9596f02489000a588b88fae4b92f955d916fdbacc48a8317357ac0,-0x13502b2d27af3de8455b05d62b976293bece0a94219e4e8a42355d38cb7400,0x48b330a45ef76a5136d2f97d770d78c4439a895332e522d900c1de1ae24e20,-0xe75fdc88221d1227ddfd1720707cbad1f48abf62cbd5f3295692dc7e4b5e00,0x277c94b47ea48d334f7c8bb52457bb4b071d785356252b8db562430ea19ad50,-0x5d8ebe9c2927d0b8623476b192c62cb01a28f64088a9b6341dcecfc3a1b9780,0xc20dad57b0ac751153a2a47dee532c092924f9d85cbbdae47e1b941691a2c68,-0x162d4d3f51b420185e42c9e70288de91fc028e95bf12ee204b3351f8137a0a40,0x23f30af47746e00d42725b5a3168234376f7f28780b81ef2e54c4650dd54d4d0,-0x33e4a8eca0417d1905ce1b2fb8a8b111b6733dac5db219cc65359c8c9e9a5040,0x42f12b13915566cec3bf7faec4c63305d7614781bfe39bb117066f43b2483a04,-0x4d62c1c82185096426bd12a7e38934a281a4d1f374b8582db76a4dc503273920,0x50560c0b49f5593feb1eb01a8a260c9438dbda4aa6ccd9c610198972045fd994,-0x4b020b6796832f1006da7893c23da1af2c24f7c9621c949b29f9639ff711f040,0x3f0c980b5a2d8c86e57536b90f2359f1878e3a61102079ffb0f590cb487c1a16,-0x2fbc4c371254921c9a6d9e3409a9323b3cbedaa6d097fd3b7e6fd0d288d40550,0x208ddca71066524ef2ada16406eb19241249e7ec148eeb7f0b63a608de5fa574,-0x13fd251300ba0cc40b6db0da04226956c64b44a33c1b8966a859b1ba7c336bd0,0xb0a77b2af465a5afbe6e6afeb3d14934141942cbcedced010144f2f3e17d4e9,-0x57a881413a30d862b983569292c464c87cba4b5f1ed03ec02b632c744678188,0x270151ae4144ef6678b744ed1806c70d6110512f319e6f2fdba501699951c90,-0xf87016693460d74447fb568e5b59a571f4c2439b887f1c0693a90c4f97f3d8,0x583935de21eb94cd0e3c5fd7c7373ebbb1d297aa8de49dce990dcf3eb75af4,-0x1bd97cffdbc1cad541b8633aa913ee8b0249863fd056d299ffc67bdea6cc48,0x7c838548f9d7ac3b04a69bf000d7e21aa97712d8b3d1532c5a62b4b0f6ba0,-0x1ea565baafa68713c0d6bdc8fe5e9bc4d9ba2316718d8656e97189d65b1d8,0x69ac815c474b1b39b799ebd5889e9cba1bd447ececce83e9c26dec398c63,-0x13cd792aea11902187610a2e4c7f7ac6a7c08537943a218fe9fd4fdd7570,0x3333c987953e87d27f36fa34dfa7d035e10df5ecb69eb8d3336d4d90ad4,-0x710d3e3a0c7540875811e1c089438dff8a71dc204d3a0c24b4eb1245b0,0xd2a8d3000a32d4e82c082a5d4da506b708246ef27c2e8c63dbe8c8bb6,-0x146a019028f4eae9a9247961db823629979e973b8bc2279fbe9836460,0x19e310f8f1dc6e661c3c2c0596bc7c6a5302cbbc48911d8bf79e0974,-0x1a48df0c1d2f3a2c4ca10d0bfcb6c370aa50ee9d488434ab97b1c00,0x14cf7aa7b9ed873d77456deb874d3236f5bddf04be51dfe54205df,-0xc6bef0cfbe37b459540ba0f75df6bb0185558a7772e66526fa68,0x5599773c68a63a367b40fa03b51241b777cd28d97fabbeff1b8,-0x191682437fac25b70d93b06731f84061663d46f9d079b20a38,0x49cf5c0989b3e420e3c4b97e44bd719f3504f7fa20068bb8,-0x79097a57f8213de8fbc2c332990bc7d9c13a03293fb148,0x5be7a9831dbd0b0319c72cb7a865faca8dd51c6441e8,-0x174273d80e273c05dfca5d5dfd268d40e55c5eda98,0xecf48dee93462810f69f60466a7d2edf3843d1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 25 70 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 70 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 58 indices rho q16 m16 16 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 58 indices rho q16 m16 16 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r17 : List ℤ := raw_ints% [0x7cdf4385efdcf68433a99e92424a79483dc83000000,0xa97fb98b8482708d802aab65047556d3c1581a80000,0x6d92da264f73c833517162215d2d39619cd460a8000,0x2ce6ecb97e1fc595002273619bce70f193fc9077000,0xd18d07e0d9fe5eb70780cb320363bc50f17fca9400,0x2e4ea98985d8c7ad28485b0208929d0ebec0c2dd00,0x80e9ee997cc9ff6983e600518baa78137d2039540,0x121e272b62947acd9d4e2c465a9e93504bd3eb7c0,0x217f0e6c073630d56a6104ef420a6da5550b3010,0x338e17a44cb8c2455b688aeeb823f80dfea09b0,0x42a2d2b8e897539f404914588cf0d7e6f8bf8c,0x48bff741ca6b808e3b8d0aa486554db865834,0x4350f88ef050dab06fd5b4adf3e0a0bdb80f,0x34dc20601cdb98890bf31a0856bb2ef1fd0,0x23329657f27dead4baa63544836de3eed5,0x13d0f4240e53b35defce9d6a4a06ae19c,0x9621cf1e2cb5ae55794d44827f51f6b,0x3b4dd777f23791f6948ce7cce473b0,0x134fa3f40fca88cb267d75b0ba8c2,0x5188a61799b4396ba46429b842c,0x1101c10d5af4c67caa2ce14189,0x2b34086a631361538de06310,0x4e8cf4bcc412b290ac79e5,0x5b1f4a8325a413915d04,0x32ba9ad06072605ca5]
def m17 : List ℤ := raw_ints% [0x0,0x2e14a6a1542612f1422bd6e5d0f92f6c0891201e77dcf77fca3d2a9000,-0x5abefc3b6a370d76fa6cc38565cd092682b76bad39ebff61b032cb2dc00,0x56c80d0efac772cb6601aec171eb09eee1fcbfcee9f64cd03e2e6d4e0400,-0x35b14a0ea3756925997cd60204896d8f0a116737d7543dca4132952266200,0x1828bfb5cb1a87706f2d61a18494e769885881e743a1eb76af4540af45a600,-0x86cdbe4da36cb82a34f48ed5d4190ba05eef8c7967a463e4b9d5d09a9f0240,0x25eb63dec57971af2a8497dd494f42d2306145ae8d9230fd30d71edae6be000,-0x8d74619e6a3e0cecd509ecfd4d6ca8d62391a373d4831062a1a9533c0fedea0,0x1be0522d836d5a0382b9d5c8ca091e5fdba6867eb7ed501423ea914afdf99600,-0x4b642ce32edd8c81b8e96d00e6fac1f6f459f6169c6a93ea77bdad6c4c5a7430,0xb0de712d95e06414c63b69dd02d9581dab8aa967441d539d2f817e62a7f7fc80,-0x16b2038d5f4fc974e1247e8468340117cfee345381fe377296b9d78224bac0c08,0x29103e4a902ed67f06d5d4af5c614556445dd0168a7cf5d1a01cf3e9b813ad040,-0x41d7bf5b5c827129d9a8539c4916a7811fd3468f4c8c3175126ed8f3dc547d130,0x5dfa627f47016ca0df355f877ffacbc7ac9e52f007ce34658a69202943383b740,-0x77d2ba873998ced33c63731663917d17aeb903d38be276a12339d676532bb36a4,0x88d98014f1c0623f9db8adf2294d4ddea5ad850a84324e37feb0477ae27e9e120,-0x8c4b1b361f98ec86297979e5abc284bc744ba50608203bbbae07fa3352df875cc,0x814a705405df00f00c552ddcb061a9540b004475ec72105f6c6096af726b5f580,-0x6b369934888888541c0b59fe58620b1a7aca4e376e1e44ec9e33cd9465ce60a7e,0x5008ead5a26bef3a376f5f6959c67e5a9c417d112d9d4b41b52721e47d55218d0,-0x35c8b5653c3f07d22c6d6995c8ba1a8e5b0b742337659dbfd2a7c1a99bd111fac,0x20856b3b75e3717b0e1736e01dfc007343fdfa91389db774492c1291194e24890,-0x11ad5dd7c93f08de9f164563f7d0aa497711120a7bbde42592e699bc50cae79f1,0x8a0273d7ea36cef9d404490bc5823c85ce5fc37c62b6f2f407a36b08c5ad2388,-0x3c569e1547f0211b5fbbdf058c96b532de8f80739b9e661ad9703a97f9a3af68,0x17947212db814806d25c6659c7020bc5b6449bf5f3acef49669028c9af198818,-0x83656377c8e3edfa2e39e749d77aa301ffc3fe967ee12ee98fd328f308f39fc,0x28a2e437d63662f65a61368d5b95cdcd1a157f5dc4f3958f0394e67871559c8,-0xb1ca61be9b0a1ac9f2e78786392f2cfc4abd8529d56daa6f0efc4992f827f8,0x2ac45938ebe646ef0308b022a419173502fbfbde36442125423548a4fa7598,-0x8fec5b6cd4d904562aded7daecdab2460b10e325902e7528f92a00ff9050b,0x1a47d5afc790d768a33fea8faefe4c897e8e619b7f348ee65fa09f787cd70,-0x42192d0bb6a422d2d92023daa2863b66e6d97b13c12b3890fc43b00d527c,0x8dae8754cc812bb5ed7e86a64686c0bd569cc5e0538973e2771bc6e1170,-0xffbc4888f25474a6756b72aaae8e90a35a58020f57e469d0503ae46a6e,0x17f205a3bed28947bacdc1b4af92e2b59ae28ae22368acda30213812e0,-0x1d4178fcfa841aa0f6f6c7a0ee134549e33f79a61ebf18172efcc6e9c,0x1c86b09fd4d57121829d81faa7d204ef1fa1b75efec2b55bc69a2e40,-0x159b4caa1017e0cb2e1395af8554af495138f0ad6e1f50bb23c06f7,0xc48b43b5360db5d646cd1917bcc940d2dce8b89e382b6117f2068,-0x503788de70eef8c61456661a7eaf9660d99e329ef25bc1db3220,0x16255fd3c2b925aa7a4fa8711ded6419de8c122de5c7bb107f8,-0x3cf20fd2ce9a73baf6e86a97d6da2f6e71761a0f684ae45f0,0x5cb953df65d29d09c1d9320842861b62d9b3e9b905debc8,-0x40b4248d8c940b535ccf60a4a96f7572ba4bcfb7f2450,0xee22ddef7682fa3dd1833cd922151a363817a4e4d8,-0x87fdf90f35c2ff30f54a3c549142f04323a59e9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 25 72 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 72 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 58 indices rho q17 m17 17 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 58 indices rho q17 m17 17 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r18 : List ℤ := raw_ints% [-0x21aa4b016f24e114211147ec6f19c167bac7735000000,-0x2daa4cbfc3e47544eac7d355c93548eedaff19c980000,-0x1d7fb2d5d9dfe9a0bbc7178747207dd9cc708f1498000,-0xc14244be7dd3fc177ce371d0d49025e1013d45c31000,-0x385229cd4482fae4ff6151319b172bc8a8bb1c3aec00,-0xc6f38514ede97267c69559a69573dc855288c45c300,-0x2294cd31bbdc3ddc43345f3008945875369e1325ac0,-0x4dad5feefbe69b48634f08347b74d774e57e70c5c0,-0x8f70d7b107408bcee2f4716d46a654aab60886b30,-0xdc7d7191cab137473ed91dee8569bb56f07fa8f0,-0x11c96e9e72b28e3193c0cf154086acaad15a5d04,-0x13639d489c129f0cad6cd2ac37f0905a3af3784,-0x11e9358b6a05c2b0b93dded2d8e39718c607ed,-0xe09e8ae51ff00f0bc0788bbeb0c78d31821e,-0x95439cfa567e320fab67e6afb25c5c7e08e,-0x53d910f7d13230ad9ee949eb16c1abc9f5,-0x279ad4ca13053c685fb85074cd8263123,-0xf99ebcd21462bef6f4cff353dfb5e10,-0x5108576c96cfdfa6b1afeef39406f8,-0x154f12453401a402542d1dc0300ba,-0x46d6307cb9409dd340ee20e13c3,-0xb325175c6c992088ae048094a,-0x1440b3d009ceca420a967b56,-0x175aca35874bd0662eb2a5,-0xce964fa30267c0ca15d]
def m18 : List ℤ := raw_ints% [0x0,-0x5f0a97acbd8e8711987a6b39ff01f1ced1ab523ed737be77911e27c9000,0xb9c462ec4bfca32fd6bd183a9dbd30734b3a4e154776beb97b68c30e5c00,-0xb04a27fc9629528417ab4112c79773c6b8817412b1235d147329e16ee5c00,0x6c368fe9cb1b7310cc9271cb92a3f13167be0846559fb96bde3bc333f6ec00,-0x304bf1fc325c05ac4f678610db71d07eea2d1da4b2e67fce1bf67c0e802c600,0x10b3dcf960b69329be5730e1c033e1289eaed9a2991af95384e78da0f3da76c0,-0x4a8764d03ccbe49df741e6a3a9f49c2c266a2c9b8f5d8a70cdf7b186fe41c400,0x11391137fcf9f12e3a5b7d9d709c16acae8a8c95d2bc20d3bbb50389fdbaad920,-0x35cfaebf3b24e9881f7342a7f335c08258d42162528217b1a11f0bea51908a600,0x902aa0ec5891d8e9b69a8676025874a4fbd7304967d8a875cbe72f6afb28f6350,-0x14ef0b66fdce702122c4154c6bed8eb25f5f1fb8f012a9cb31f4a11d8ac1493f80,0x2a8c7ae32b990a7e8799dfa40bb02bccda1b2a2f8f303091eb3bb26c70ad905628,-0x4c305c01a01b7fb13c8378162dbff14c0698c44334e0757024cd21364bd09bdc40,0x78dba3876d2a9bd62f3777e79639a3c8b201560832999a6c046d4434c272988750,-0xaa97a1c2e109baef4a946a5b29043d10369990b66df23977f2031992dd47e29240,0xd7033ad54a6acf9ef378ff06d2e08715c8437eff458c90d1e667e13d9d4cdef544,-0xf2a4f57262e4ed7d76c4370a10dd97361b7b7e0ca9030c5a262a6400343b8e9520,0xf5addb35b3476e988cfcb297a0936368b38c5d5f9d87be9740e4860e7eb0e37d94,-0xdf81b4780eec1687f30a7968599b5210b44ef7626c824999ee3ca41ec056a88440,0xb6de0453209be1aa800e317b6b8772d55cbd549be9ad841e0a4996603d663fbe06,-0x869cef9b0111dc3c9cfe38ac895397392da8afa1a3c37f41b3480f9831fa9c2fd0,0x592655a5d7132170859b2702df097f8b8a2f6114c1bc1c99dd9878fab6b70bab94,-0x3516f305279645023647d356d7c7decd75b050891cb3d9f817ea72722e13f5a250,0x1c66987e01598b40434625040383ec527a0c3a4bc050c16691e2464fb27fdc4a79,-0xda0e6cc9e839246ac3aa83a90a8c2aea5ed46a67795badc8221367b393a946088,0x5dada4c143b7c69e7ccdd18ce7e1a01f4a082bd4d39c1c5686d630f3664f38ed0,-0x23f0c5760867c326cdcf25c9e3cb0889ced2df6879c1eb4fa2462c0b9e03caed8,0xc46d000e7031ebb840190d923d44e9e87ad08bb85275934d21170e69fed67364,-0x3b8448f8db37f2b4ce78c78189025a2b71f6c21a05bebed44516954bd083bbc8,0xfed1bd6ac5904fbf558e7a63679fc8cadf714b5a429ad6e9de81a33302dad80,-0x3be7dcc83f178a79d9dc40c6baae41ff6c91d0430b470cad91414d9fdc67958,0xc4beb76da4ddd6e06e12acbd56af39ceaccbc258eb4f1681309741959496f3,-0x23013fcb517494bab58d9e2547adbf829d8d02db4faaad7abc7484fa65cb70,0x55a18ac10789e25714bb4e92edf696cc14acaf880dc18daa953106b28c254,-0xb22b7c50f8511f42e4751f1aae34aeb7430c5ac0489517e5bcbbbb790bb0,0x13777b8951758afb38a33931b597f77e7e68c8eb036429206c3472803306,-0x1c2c5b078e71d04e05532f1b45c904da533f7c99848c52ac6ced24adde0,0x2127d3a07b13fcdd7c870510a1fcf3d420c69aecdeff6afbf53324c754,-0x1f095362d539bdc7363cf5c82f9b8db5c7991c74d8550476409d81180,0x167b6179367a5fafef08496bcbc2334d52851920680b9a0ed618dd0f,-0xc2b6e0575195524cc2d6119109b1a12c56dcd0a71f268053003168,0x4b46b7a4e04ce9dd3707cab783862edfc8e60781f6f318b2f99f8,-0x13914860277cd35701a1fd223631c92a4a200dc0550ce6d89d38,0x325983f142ed30474213c56fe430cbd0e93dc8ef725195c648,-0x470b830ef3c314a057b3f9fa3aaa5d168064561019286bc8,0x2d8c54cfa62dc4a79a8d3efd964cba96eaab8ab6966188,-0x985840d4357bcc106f3baafc69dead80edcdc190518,0x4e083d4d9c3b1824e611cb8a859d5f0d45845e41]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 25 74 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 74 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 58 indices rho q18 m18 18 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 58 indices rho q18 m18 18 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r19 : List ℤ := raw_ints% [0x8918e97a3d7d46b47d3e8247022d4da3cbc79d6d000000,0xb9d927bf297de87afd9989cdf62423411ab7fb66d80000,0x77f8f5c02b4dd34a7a41e13c7d5f7c5a2351e5135d8000,0x311699f4683f6b0608885712efa653d5b8814022ed9000,0xe4b5bcf1b865f86a015a1f53aa4fc8367c74138deec00,0x32737f24b93f87f4b1faad8a0d9274b61f1a489175300,0x8c2dfcb6e35dcf639aed6660af9cd852c0db605b9ec0,0x13a8fa4d9aee7f9d881edb14ed8b30a7018e46d54840,0x2443fec0cf5328b21503bf2364ecba04bd12b0e9fb0,0x37ae2f2ea6cf6d83031ac93ccd9e8da6797c5905d0,0x47c6a93f72786860e1eb5d8428ca41c1d7d093ba4,0x4e2221913d803c36d7a6a57399baac6ac55e478c,0x48114e7f583b77e9b1189e9c03ec4f51a90aff5,0x3864b9cf1d8c13cab97f107051e70323937db8,0x2568150da654e797b895e034361a00fe62690,0x14f88a51fcd68ed71836aa73e4208eca35ac,0x9e2302aeea4549a81fd1af5d6cd1e5be72,0x3e243639e074787740a91ab0c24e082a0,0x141e21d9410ab435504a211ed274a658,0x54631a0e1b1b5bf5c45ed78f12f524,0x117914a61fba838cfbffd1090155d,0x2c04a52752b8a7d32a7aa0aa398,0x4f458bb6cfbda5ca4f7a3b02c,0x5af3d1a535ee4bb4ca7d8a4,0x31fd9df8d731bffb83914]
def m19 : List ℤ := raw_ints% [0x0,0xc405d8d446f5f6944a7c7d279df402ba907159a19be2f8d69b4e320e9000,-0x17c5a016ade8f3f678f5f8be7dce2cf158668410be364e95e8e88124d9dc00,0x1663e08a57a2815c1b2256e3a0ddf381bc0c465ceeb9e375da42bfef0d50400,-0xda3540d04423e1433f117fe34154f385c9a7e38c1ecfae2c8ff2ec596596200,0x609dcfe73b6e1f1df2b658a1ca2b5a7210054b11379668864e7e1ee302c83600,-0x2123f64ab1134ae1d817658ad7f5b4762c50159697450d010f237cf3fbeb2ee40,0x92a22796ea580c9069c9821ea80399e7136cdd1a83bce0d2db2117c00a26bb000,-0x21978b3ddf1e4f1cfc73e0ec5cfc5608ecb6f05111f19ac0f94f32bf964238eda0,0x6804474f311a217c3d367f1e998c6535222f481e790f5c73628d376a762843be00,-0x1141a3394204228a66a3322693033f69b492dd023b313515df6fcf639d6c4ca1e30,0x27b5ad24c4ec00c2548d1ca059d16f71326ad0944ffdbabb69fad8d174bec71a480,-0x4feabd19641bd93f38140ca8ede0834995d33072d0b11545015e4e38e2997cc4ac8,0x8da4e9b3d50046fba6b78deaabf299c25460460c0abb16c5608f0cbb15c40265a40,-0xde5223b64bc06eddbc1944a929ada938e9b4921e58c7fcaf47d5d32393cf746cab0,0x136619e9108dbfc127dc6e30eab68a6d29874aa80c4640507488ee4e66923ca84940,-0x182c56a3e9ac4b1d2cd00054cb0347e07a09f601507a351a34e6796106ca7abd01e4,0x1af588e986483b8f66b4daf694b7b51d0dc3dde2e1f5efb362646a00c40983138d20,-0x1af685f50ea482390eafc8e1964bcc29a59f05b6c3f9a419a45c5bfbef33752e4dcc,0x1837d2b05c43faebfc79a4399f756ebd190cdf3c7355f373b8411e036ddd3bbc3980,-0x138d7565f17b8ca04cf4070c69b8d3fa5841971be5687a05dfed7b6126257ffb6aae,0xe31da5b82015799312632915155fc8815a3e2e6d2febd706f8aa2fef67fabb75950,-0x943f5d1d8dcbb0f570b2edf72f6cb147a5a67b4558a129577f7b73624ffb5e5da8c,0x56f4ade9dcb2fa892ae1bfe3bd01a3a574fcfdf71f6a387b4a2b604a661a6818310,-0x2dc92e4433b5f8370e321fe9c4f9b57ad5da30630da55808062f3c1753382c72581,0x159bd47108475ccf6da1fccd92578818d36c9eac09e2232727f511eb6ea9b5e1688,-0x91f5e174bc23657a213e385baaeaee67b01d49cfb7f8bfb6e083ba7530ecef6028,0x36facb6cc24c6453fe3d8d10eadf827d1b98c7961671b06ae40b93f33708527318,-0x126b7deea02afc3762a97f8bdb409252f5910b536eab9d7095faa0eb17410b802c,0x577ddad04c648203cf378c89d3130c21a040a5bd9d67025f7c7b09556fc5bbb48,-0x16e928c4a24e5bfb9ed9f9cdd8cf41fc9a9b3f9681ca9a30809bd12eee88ea818,0x5438bfda91dd661a6bef962da3801143641d3d4517569058d45e319b99026118,-0x10dee8ad4e2436acf7bbfd67b91a042035f98ec43e670c53d8f1cdce977ff21b,0x2ecab1bdd179582f8166a5b68efb7e3939f65ba16397264d788f6ad9049ab70,-0x6f521fd2840b414cdf24993f53bf02b6b99e2c190e3c3dffd51c2c79b88cfc,0xe0cd84a5d032609da088c4e37f753a5c8cc46f53e02d0791e699088498770,-0x17c8c23b3c089aca0d601ffcfba4c4013f8aaa7b460ebb5d091f0a77d057e,0x213ee712f1b20ca35f5f700dcfb7ecd53b2218b140d80455f0fc19844660,-0x25ad50ba132291c128d14213bd8d30b2ac204444c99b51ba7ddc2665dbc,0x21d960f9532d828a564a11e03eb18307b351b13e26fb506e051c346fc0,-0x1770f8d0a72f302fd7a3e567ee36f9574e89a01d05adc699ad5b4a727,0xc13ac2b95aa6efa91abb47084f6035ccf82949195e4864c82f84b68,-0x46bb2f22aae7ca7a2be4a9fec5b7de2f06e90118f52ff6e372e8e0,0x114deafb7749a5914f046b5fc4fe9443153e846a6327c1f4a0af8,-0x299d99000e8281efbe970d9f9ffd01f5e6dfc4f94857d0955c0,0x3670fd743caacdf498ca85bdfc89616233ab3a53c05b42c48,-0x200f4988cd17b20e9d0c94346f3daf156edcadbbe4df0b0,0x617026dd5d801681437dffb16ddcfa5f7486f38acb58,-0x2cc41a8c4db1cd04504d4dc803eaedfe44ecbb6d9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 25 76 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 76 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 58 indices rho q19 m19 19 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 58 indices rho q19 m19 19 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r20 : List ℤ := raw_ints% [-0x212ce00e32b2d9503683441599b42fffece0d62b54000000,-0x2cf2225d23eba8f46de1a887f770182079f87e423d600000,-0x1cfefc882a9dc4ca5d18ada9c6523a9bac8fb99233ae0000,-0xbdb26623f0df52750ab70da421483f80b8413eacee0c000,-0x3732e87710c0910e9ae1dcf6ed26a33aa4401cd1f39e000,-0xc2ab00a13138b149b16af4b51a8240cb07752da989f000,-0x21c6e30137fc47130429272bb67477e02716f245206c00,-0x4bb9b91188b347673f40135b3109e3010cac5b72f4d40,-0x8b8c2405746424b58bfaef9f0f8b1aee960315fe7b80,-0xd6064b241317d0521888620389cb4de4a59254d4450,-0x1139288e28f15c72020932386a2721e7c2de96a3f00,-0x12b9a03d79397c1ec16a692fd6e08a832c9594689c,-0x113f68902ffd9b43713c0216aa92bc050e1882d78,-0xd79e9e23c4d3569911eaa9d46266e98d51ae33f,-0x8eca033f1ba60d76e274d30224094dbdfd6ac0,-0x4fe812fafb55f64bd68124185b0a5e2140998,-0x2595dffd1345c345d1acf5c20d3c765e10d0,-0xebcc4864821cb9f689f977e180dc4700fa,-0x4c2727c1d58693d7a43618e210be85c00,-0x13e94093f5248b1e24187140936f2d98,-0x41c416d03a3f3eeaa05dadad40be18,-0xa51ebe732e5cb32a4fbfe45ceb6f,-0x1283b041af8aca4b39770efe100,-0x15268ed98a7bb8802d8752efc,-0xb914b521b62bb020253560]
def m20 : List ℤ := raw_ints% [0x0,-0x1944c0f35d25b4c91d9a0c221b5c745a0c9e9c8dd5184213aa051473e09000,0x30ae38db36eb3d06f60a8246c26ad016bdbb706288500215305f8a5c0155c00,-0x2d83d768f87dcd5212e32a66a175df42cd7637864fc9c8c81d87b9fe92bf5c00,0x1b83ba8e524de5264519698d07586ae49abc60bf7e8f0fc1fcba343252e9f6c00,-0xc1690612049f884f62216d994f3197846a60b8bf3de6e55658ed52b5587df1600,0x41cfb5cc60fc6be94049ec1594e76689e7090a276580452673fc5cff3f8a24d2c0,-0x120ca082e43c104721c6aacf0057ae209468b5311261fe8be28c7fb6b2cc2d49400,0x4198823389fa6dbb007a274b542ce6a9432619bb5f9722d570f42a450548fab7c20,-0xc9555773998f11314be845a79cfff14a5e49f92002fd61e41cef81d99a9545eae00,0x21193a5d7f4c7c562d8dfe15973d173250ca22330ecd7b009e60e5d3ed679ab82950,-0x4b739602325babd2a61c2b27019f82a79951935257464867867dd350d0196af9a780,0x966096219bcf9f9df37177d28c030d229995c29ecbac34e44c362c2bc7816b0b95e8,-0x107dac1ecf0afd715423394dfcb6a5247081a1bb02338bde1bdc6377a900fedbb7e40,0x199d5fecaf69a233cd555fe877b7aa37a648eb3b57e6d9c8c91098025ab9df765e5d0,-0x236019bfa714c16d362a035c841ae2222ef449bb3f9d696d6ba574bcef7ea81dbe440,0x2b96c7bba3409d7bea1c048bbdfbb8f277df98a789373fb01b485a2df3a8563221084,-0x300c464400fb54a0a46762372dd8065a12a92c2feddd91f9a0f8b73b85aaeb0d7e120,0x2f79771eeed76d462e7d20425673935337d7901f3c28298b5009583b4ee776c291194,-0x2a1af8996bc6cf4ef42051005b08e4a66e7c80deaca9c58362dff408933765c4fe840,0x218c738f425a5f42b66e96e770a9f54469649b8ad57b1a07a94701efc9c7c7f38b976,-0x1805ce98106c5566f9566d105fcac1965e119d264d32efe81a339b0aae845b6ab3e50,0xf74e899b03c6fbf925368ed49041ac70103f27f7e98828800881116c0d0b969a98b4,-0x8ee4b16b1700ab2bc974100e3f1b3d856aab88cc45be82a5885778e7d77f15794cd0,0x4a0ff0579e834d6d4ac772320df21675f0f8c1f958c315d90a7bec8df326fce02409,-0x226150dd965fdd4f4dded7e97eb7772b485ff6e40ee8e718d0aa717fdc574b466b88,0xe43913f9eaae42d8e150b46a9939786d99d77178a94e28cd89d10f85915f88c6510,-0x5467cf5c0c958df2ce862cffd6a24dfe2389554558b16a007d85cc6a4c49babedd8,0x1bbcb986d0cc662bebb98a066715cca1bb5a70841387fc52b329470c27d0f9f0e54,-0x81154abd61c56797c1464b7f5f4a13d405f6c1f8feec69158eeab3a9cc81b1c348,0x21140c89713f7ff7544bcaa93c9205ef62e7f8949d1bdd483ea8ac3732092f1660,-0x76d5e4e76db62bcc84fb4e27afc392891939ec3fb59e9d4d49a8b35e916be90d8,0x173aa29be7af4e7a1cf3598b68df9a48ade2fa269ba2243dd31852895106a6a83,-0x3ec423cce5cbd5eee743268236798d1cee27d6737447a888d229c28101c0a970,0x91355dfb933e03a351e167826339f66a20f267134e362c717f470db83f6b9d4,-0x11c907984644d7fa090e261aa73838bde949f876275061931c298b904b3a9b0,0x1d26194ee4855d0272deaa0b88bd9783e0a67afac1720062d1fe3112a7ded6,-0x275811a09a3f50cbed8780eb6b73f8748d8f572027d1f430d1b4b19672b60,0x2aed5448d333d91eac21f672c76162cc565ae02846f0ed01356f2eecca34,-0x25009efec709b888eb4902ee4477b83e04642f77ba70ba28e545e375b00,0x187d758af2fafd8fd045dbbfda4d3af17bad0b2e5c05a94523ab7c7e3f,-0xc010abfadf781604720d5216823774e87f714b15694f2f4ce218c468,0x428a8e82bbaaa7cbf30575f0cbd704a69b99b6af3cf1a1ec465be38,-0xf50ba9f7558f94aa53b1f8f724cd6a96386497d8898d22b248438,0x226945194cb319ed0e4bbe4258b6fcda6a85b6f6b29d296d3c58,-0x29b8dd9eea28f125b27d0c1e195628c24f577052d0b8aa4648,0x16900c9fcd2915fc92ad3a13cd67866e2b9f799eda320228,-0x3e4e59a40ac044f1fc1a91cb38607405d8d7d80934798,0x19ad3e3fdcd1769767c79569d6e28a466e5b00d9b1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 25 78 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 78 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 58 indices rho q20 m20 20 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 58 indices rho q20 m20 20 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r21 : List ℤ := raw_ints% [0x7ad33b45be2b4e884df6e8c92a3373e6f9b5eaf0360000000,0xa65003602940e970187403f8a4bbcaf5b362f57b3e9000000,0x6b3b1bd9aa2487d96d3fc305577f5a7a80a6b70ff87700000,0x2bd14b983b6f169411fec00ec40dd71cbac930f1045c00000,0xcbdda6130c6cdfe756e4717943ecd5d640fb5afc978bc000,0x2ce71a3f890822b5ee71f185368f8eedb8e32ba781e94000,0x7c8f500c0cbcc4200d9f74776e42d9fe1b8aa5035de9800,0x11704d1f9980462db8a1da2bd0ca2df9cbb8e129d8a3400,0x201b5a491175625172f770f4993a8274d85c0cea9a34c0,0x3131a8c46240ec0dc2bb7a09983b37cae8a8213d86480,0x3f46000f6ced100b69279c9a9ff9eb85099727014d30,0x44b61b3978185411a6dba01868337ec8a4aec1cff00,0x3f35f2dbcbc4193a62ffd8ad1fdeebb67710515544,0x31524b131b6bd86ea4ef31592caa34fdeaac866e8,0x209d0c058be4c1ad064e471f57cbe2300592cd01,0x1238a402e8c6c642165684fc734ff1a05ac1000,0x88e30ba85c583baede5b7842da323738d9c88,0x35919a47ac315f14b69c0519abf21845b5d0,0x11435da1200a637b5fabfd4ec79819afa06,0x480bcee583e0ffb34dec4c79113cf6c80,0xed55a6708a903fc38d4b6eaeff43288,0x2521d5541f2357229d31e6dbe80d88,0x426505a48a40d014b3a8ff1d13d1,0x4b9046e969c80a305b8dd2a1c0,0x292689dd7adc102f13d946e4]
def m21 : List ℤ := raw_ints% [0x0,0x341dcdf5f01dc4decd0db906586eaff9ba0722e4878208488eaa7a2eff29000,-0x63b4929d01bab99394940f2daedf73f8d62297cb3925044bb3c50d5dc2c0dc00,0x5c8df4938d2e46344324b934636f76646557b6ebe12e4f2c82ee2afe04c9c0400,-0x3789cb84a4e2eb194987308d219026ca69c148ca8a09fa915da05075a758ac6200,0x1836f18cf9864cc4942dca6aed3cdb560a2c12cfea3d98e551abef735cffbdb4600,-0x82cc90aee1d8c1712fd4cbc3f94d397170e72c625db45b56aa2f3c51ddcaf2aba40,0x23953c05ad397965181b2648874e6ba8b281beeb2a2e185841f18dba6a3a6c800000,-0x803d25c2111e12a69227fbef0ce764abcbfd387ba2e5fa23b587f760a9b711c734a0,0x18636b4f3f3ddae3f2445fed8470dc2b92b0df02e9275ac8e3757fe70b3e55995a600,-0x3f94237dfef8b28ebdbeb5a9a27b32ebc33085de0ba466160504c1a1d1e66aa2ff830,0x8f996332f9b290bb595a2cebf57df8aca5fd33b0784864a19f74359a11b5c6ba20c80,-0x11b7818d708a6e7973281687b6085f2a8ff287c0a07c934eb22e5a0afbec7eb547c788,0x1ec778a4578b32f794319b771dc9521c54b9dba79614cf831d5fe02c7602f065257440,-0x2f51906f96ec742d0accd6fd525e4acfa72115148813d656d8bb601d11a4e0ded89830,0x40a7b6726125bb35819bc79748b7eacb2bebf1eeab370235cbaa8c03c5eee56afaeb40,-0x4ec99e051dfc7ce3b72887b66d46f0949627112489e14c18aa3def3b2587001e307d24,0x55d9b721b118d6dd90b85fbf22660a4d5d27521672c95a8627b9570c34d2342234a920,-0x53d005ce850803101c0a8c5053d7d79ae8575015333b0ea014111ebffff3704d9ec5cc,0x4968a60437bfd38ec584bfe7bb07c073a157973a588f5783909f0a27f36aca5da54d80,-0x39bb395382a04801e17545bfc0fd79dd506e83da5b8b3b56b0693cf45788d5dadaf45e,0x28c74d48a3f6a82bad3c5efde015bf6eebd21d4a6513f4a4e176996b3d8facc4662dd0,-0x19dda9c78e1778b6d353a686e1ad0aede0bfe5c4e4536108d0b740703b4c0e918bce6c,0xeb9368648a9ec89b625c52c23f2d4b28f056ccf3a0ea269e746a9021468a800907190,-0x78335246bf2f62e6acafa5bf0c6ff726c385b64ae7dd5b9d0b399be740430c7f6a911,0x36e2e1fb0e479ca0ee272a6611e81a794acda11f3fa6047e0b942e39b380be35e9588,-0x166164ec3913db374338cffc9734ff55da02c212207fe2fd7ec6d22697a7d92aa40e8,0x8209755c7197fe560c3d560a5b11d8d2fb76c8c780891ecd5353e864ed8ce9116218,-0x29ea8514da02502f7ab3901db34f0e65795ca43524d5cea6f83b10c47cb5ea6a9edc,0xbf2094cb0228f5549d1279feb8b9eb7f682362baaa461545d0281dd1eebc22b04c8,-0x2fedbf62f2dd4376dfea9987197700aa3f8d1c97acefc66cf5740d623892816a538,0xa8451df5b7e9105d27491b070a681a438a859421ce82209663192abc21bb125c98,-0x20187786e001a6dcc893a1294ef2551f1647922f25d1609ac565ff191bc999882b,0x547b6f203e2cf6eb92fca2241f7e8b3755bedb0bf0640da2de7bd919a8622d170,-0xbe0a2c8b71cc86f358d19f04a93283e39f52108f13d2f046cc3831b36cacff7c,0x1695b2716c3479338a954bc3c216e47bd7ff35519e6d8161b962377a07f3d570,-0x23d49bea91e91ee7a17446ac976516d74e2dd04b43cb09cc315bdb8bac5630e,0x2eb0c2d765d78730536cf8a4ebbe7bc88226563eec98fb81b2388742d19de0,-0x3108415b169a18d790501923d6528d9715a00fed3be86aadc19f88cf20fdc,0x288a286b06dbc4a583349c7fba5019b22d8179d75d28893e75cabf9cc540,-0x19a25f8c02048fde343ea97c4e70cd49170ea4afd4af49c2bd188d33557,0xbf33098b0afc17c998976b99ef4e3c4ebc2901eca482e738d0cff3268,-0x3eabb5b5eb839fc59712ee9c73f915a9c54234472646765285dcc7a0,0xd90a7fc7741b13774560b3124a7f2f5fe8212834127d6fea53e1f8,-0x1c76fb61a1781321d821b0891f67dd132475df4e716977fa75310,0x1ffa0c4ec452706dfcef028933f0d1726691879f811739efcc8,-0xfe0711f1741ffa310422d90a8c916d810a55db2b1d7a3010,0x27d502a13bd6c2cba44aa1af556ff4d97f64ac894909d8,-0xeb98b41b6fff7007819f617964e1ba94b7c3a8ccc9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 25 80 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 80 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 58 indices rho q21 m21 21 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 58 indices rho q21 m21 21 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r22 : List ℤ := raw_ints% [-0x1b4f079b44c5c7361d2c225cc66a9b7952e4db1fc7a24000000,-0x24f576f804f40fe77ab90bc6b09492c01269e3796e047e00000,-0x17d101bcbd00daf1149145b7d99c8e1f3ffc6c0525d94de0000,-0x9b9f3d8c4910bd57ab1de8d36c9386c99ceb6f1a783bbf4000,-0x2d397f8c433e3c98308638995f3de5398cd2cf7cd8e9273000,-0x9f44c868aa4022dd166e4e9c64c7e3e984a8b770f3aa90c00,-0x1b97d5fa6eebf8e64df6289304604a57a25db3818eb3e9b00,-0x3dc2ed4ca28ec1dd8966a5a7e9725641a9b65c3d232e8400,-0x719d7e81b728b4766401877ce5d417e1a8afbde67ee66c0,-0xadec4ca7262d0abb8842a70b1a426a38650784edb0bf40,-0xdf7b3edf11dd70a51ecbc9fd5c60a570f8a592ae80990,-0xf26e691de4ee9752950081d35571799efc4ab7e82010,-0xdec49e5bff98388ba327c4d2e8ffc53dff9d7ec8594,-0xad9a605901cf8f61c5a2622bdc18a2e108e0da5040,-0x72a37352642a9c4de0d8f350106ccf595e6f8dc70,-0x3ff45855e2ae43b3d45d6d408d74297acb6ab6c7,-0x1dfaee3839fbe1d27cc5b414f2d12c6808524ec,-0xbb62d29890685ecf8bb1eb443b0be31566714,-0x3c452d52fc211be30ab4341816fbc87f2f50,-0xfafe9b76a7cfd29f4f50e7f0d0cd163baa,-0x338df3dae602f0cf6aa671c725aea902c,-0x80b7603189dc62fd6d2a5dd4e948bf4,-0xe57a6d740ec00506d24e195e09e70,-0x1044f719b186b525fe545f3cfaf7,-0x8d3c1d1cb2d43003026c3bfd4]
def m22 : List ℤ := raw_ints% [0x0,-0x6b7d78cb3f3d660b86ec4d9d16644af30faeb7f7577c3115a63f9c00ee449000,0xcc3ee915947c362ad4ae2445b4732cc51747591325dc58dc22c66b9161adc5c00,-0xbc4562f2ba8d490c2325b0046965a53ede3b3fcdcbe1e35a5db74bb7c6bc505c00,0x7028d588030ffcd95cd59ee2184b9e941c246c197f11b73d67ee3af6e51dc07ec00,-0x3089b52973cb81664f3847fb63e94d8f4ef2d7bf1ebab2b96fa364f88caf0099e600,0x1042ca1b8f0f97238a403e7eaf61335fef4dca7f0da8d9664590edee705b608178ec0,-0x4637d73ca79a402b38f4bc1601a01d37cead87d1b407f63e288feaa6a179a53b7e400,0xfafdf5ed256850741da381a83efac43dd0e3f0bb776e7060e50b690e2474fcb26f720,-0x2f546f6d200528b37006d871ba55a10cfacdf4528844865a40a139459a04231eab7600,0x7a4e5dbf612139f2d255da47ea7fb94af75c4efbb9a243cdd74afcfa53463259977f50,-0x111bd68fb572bccadf9f541402917c25a26f0f30f070fa3be35c509700ce19c9b82cf80,0x2174d262a344db952d9741bcf302f021a93fb438b7e213c054b42b86634773f1dce9ba8,-0x398ecf4f7832f33dc94e42fd46c727b3b2fdbb1769f3c8db75d115c90a32e90f9f77040,0x579803ee3dcffb386e903f5a1a7ab9c0a0a5e824ea83995b312463a6d165f560c2c9050,-0x766e784cded9a7e3f0d1b2caadf9e451725647c9779ab135b3b99005f2d239135b4c640,0x8ebee078e58694185b2b65c605008b47784147748ce07dee163827cb1c43f0701552bc4,-0x99c72869d872ead3d2a1a82432fafe0dafdf4c8c17bb02c46248493016ff07fb35b9d20,0x945aa80cdc5d0b58282c52dfda825cfbfa06ac9a4b046024762b9fe36707674058b1594,-0x805683d0edd631b0fd9a00e07cd42684c10bfb9feb5c7282b64b065a405ac750d419c40,0x63a1b1ec6fb50aa383a28a03642e4e0f80c9ffff6d469cb421ee34b2660bc843b1b6866,-0x456dc493541a868f282010f61c32d0d804466f1ca4f6b9a19e0e23fac599bc87dec50d0,0x2b6b52ac1248f5f0ec1ddeb37aa522621f1c656b82da290264b538bfcc7e75466b5f4d4,-0x1859d5bbc418b5c6db2ba4b36ed06d0988d7ca1dbd8430def3ee5a44168beec9a8d8b50,0xc3b8bdb1937e0d05cb6a242bcbd9e13b5e3eea5b7876eb0e017f25e1a8be8764d9c999,-0x57eae6fe5f38b67759522a831446d0598c824406a1466a86053dc903bf820b5e7c4288,0x233c4eb3448a3a68b8a71cc3f632c0284bbaddca23d31e63b6c29cc6196d437d567f50,-0xc908657f6bb587903419ba2bfe60cf9ae845eb21330904e6b2abc9fc1e425d95b90d8,0x3f909a320f451b578137c16d7cee0d99a27412e5b6cd9fa9730934fc9eb05821c6fc4,-0x11bfcf0acb7fde3eccca7d5727119ca13c607b9a51cbbd88ecf298743d5a48ac462c8,0x45b09d2c00efcd16756dd727e9c179f55ce27b481266771b9b5df0c7bfb67f9dae40,-0xef19349305b93b3b546fd200500844728d60d30ea9eec6f8b2d626838112f7a3858,0x2c7fa0384bd1e84e958ae23f55517873682edcfc6f3f17acca0f3ccf98e0f974713,-0x7217a0f45c8baf57710a48872705dc21bac52383bf35d0219ca2d41d0752a3cf70,0xf98473362d0fc69aa7efd83a11b18dd9bc2cd0ac60570120966562f26fd8af154,-0x1cc4a46dcdca3659eea943757945ca06cdaee1eaca16211ab9772c58c7c7d5fb0,0x2c2c10ccbf27427b3c085c65d651560c40fec49dd51ba65826ece74e36367326,-0x378edc22edfa24e1924106bf35084abd5d528d308f6d4a9aa3cd892298c6ce0,0x38246c5ce3a6b20e4952817e13f15900550bbf1b26ad7b8907425a64772a14,-0x2c829cde7203d66b6928641ab088a165ff4279788ce2e1ec4bff4774e9880,0x1ae165ef50e16b9c9a77a82082f2fb51e3e9ccbe179981545789b660716f,-0xbe9cdfc8983a0cbe198dcb072be778ad7817c0c46f75c2e4c43e07d368,0x3b169a3bc4fc4d581069fe33d7c8647f78d3da12fad2eebb37e807e78,-0xc05e704686b5b58e5657d44ecd7ca95f45d27f00e14ac7be7eb1f38,0x178dc6b4f65bf026ac81388aababe7a8eb1f58f9559f6f2c7e39e8,-0x1882410d788b3945fae1afc8d4d332039cd74924548529fe00c8,0xb2b9b94d87f4e6bed9ad0ea34f3bb5e3eb38f8e9856e4dbc8,-0x19757336ade99724c5c559ac7f257f36907ee1469a42218,0x8714fe1dec9124c27b41e9c3fdd456865c5a31aa621]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 25 82 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 82 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 58 indices rho q22 m22 22 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 58 indices rho q22 m22 22 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r23 : List ℤ := raw_ints% [0x5dba42c5897c9de48fdd0db9132cc7945dec9c3c420e14000000,0x7ec9c74ff2216b6cd14baa796484c0a57714468f6f3c20600000,0x51a94eed0ddcb8a65fb3310f61d84b90af891ad5ef4efe460000,0x2154dc06f8d36205f3747ac20aa30a931718080beb8690fc4000,0x9ae3f849a1d16defc321c12f0d1386813c059aec3264c113000,0x22123f74b2233e4d1e9b0e13134d57c0628535e7fcf5ebbec00,0x5e61a68a35d1f0ff16972cbabed9335d5da49746a69084c300,0xd319c28fa62d570432f5c5e62c4678137b3448660dc859100,0x18408feaa2ed556816941d620c1530fc76242f763a61d83c0,0x251829e28041f3b1f977db7b873076076d8cc71719273d40,0x2f9f09632e82e276a67604a0caf4f58c68c4fad9d619890,0x339be340cca4319053b6b4f32e1f55ebdeb34097d6d6b0,0x2f5f83a18affaa9a77847e8a804f590ab1f7c77ad3cb4,0x24e032495b2791def5e489d38dc32117d6660c02b260,0x18521cc214cacfb388179e1621651f8482d48fea0b8,0xd8cc119b01ea539a68b42a0707e2bb84960e08138,0x657ae93e06c9ab437638743266ab16d4f863eff5,0x2794523358003633a4fb97bbce435fd63e38bc0,0xcb538fab1e5a2405a43e218f9351f32914d8c,0x34d1f669a89927f7b5e9fcbce48321fe85a0,0xad38a759d90d65092353bcd71acc1f8bd2,0x1af782b0d72c645fdf3d7a4c4244d8be0,0x2ff3b9e2b42158864b2b4381a1dff24,0x363cae7f11b41e139955d6fbe7e38,0x1d54d618c251d41646b20336acd]
def m23 : List ℤ := raw_ints% [0x0,0xddb2c923326ea277c6476013fe2eda9550585b6e2470253ca6e331c1eb6d69000,-0x1a276b62004165e8d3b20b4bebbba277e3b4327b77e16774607b93ddbd97667dc00,0x17f191c5346af0911d460233f41f7d092bfc3133e96af7f0697a7711205cf0a30400,-0xe29db2c87ade247feeb2529d09ad7c4ced22830c2fc306ecfafc47c982b9a91f6200,0x615b48118f42a0cc1006127285c1cc52863bb2a0fc385af5541c5acf3028642a2d600,-0x205ef27bfd5061e649dabf0c4ab40ae62b8d19168d707996a037d20dfd7c68085d6640,0x8ab33026aa68af9a1f40f14c08e24563b7f89e358f7db89cdee81a371fd976207cd000,-0x1ebcceab1536bc5c6c6f9dd942211642d21bb6d73020e9e9c3a37eb29e6acb73a3d73a0,0x5bf839058a39c006662cf0e5a5d5dd25895c23419d4a3f8999e19aa8067e4d9b9e54e00,-0xeb9e66b098df3ad92625f4a540a308b08e4323028d268c661d3450764dad67549728230,0x20aa8009dcc89a03294ad56901f8adf519a5a68a73d0a275e16f9c52745f0c72750f3480,-0x3f4a033211973ea7460cca834b59f5f61e67f48e8d5ab73339a2fec37c081f45d1907248,0x6bd6bd1f516375c027c262bcdfba2c2fb585ee4fa0fa4571586cb5d6bb3c991bc9849e40,-0xa27b0fa5507eba558998899371812fed862d83f269ced89548cd7519c429d2e9088c99b0,0xd9692737afa9835d6cdbc7ce8b7e51aa8510c212086f68ce34486fc48808b21aac0e1d40,-0x10339c596d04370ce244af86891b0a260aafac8c084fa0c2edbeee511ad08e13d4110c864,0x114217640cd2fe2144f62219d3d3cc404541b3529829d7f544011cfd8c94112db3d1db520,-0x1074760b959d1d72d9c9635ecc7e017c1b7b14cb638e3d010135fcfa570080499b46eddcc,0xe0fab0d7fd5ecfc6d0c61d84ddfc36f3af8aefe710feb01c91166342de3df138fdd6b180,-0xac6e4614ff53feee8296e65e049064d618deb8f00774858f8d79bfa34d6c5aca843e138e,0x768ea92846e34582d680ca90fcc3dd1d51528285784c2db1b45cfab21b15c4f6309f3650,-0x491b8ef9a4bba92fbbcb99827354b98af711437ac8160acbb81ca75e5d5b541d02cd334c,0x286687bfcd586ff0670b3cc76d0f98594ff2eb0c030603b117da2035d021b63f7ee33410,-0x13fb954e20dd759b50cd01b11f9ffe182e5925fd556e15fe81527ddd8748b19998134ca1,0x8d4b3a7351cbf7b1df1570bffc6ce4c91ef319c37e35b889ad73e6aba43f01ca7b74088,-0x37a95de6e6978182f08e3a0802608a6ea4a3be1046a233bef03d78b5b36eac79633d1a8,0x137da1e666397e5be377d939c8ace3efb37995edaa924fc70b9601bcfbd5ffdde373518,-0x60ba1bd564adfab4864dd17bbb9cc5f764e31a733c24bbb701b699706945dc61c80a0c,0x1a76ce21aff91760ee9b537ebd899f1a1f70054df31a36d8d0abce4487ce9582ee3648,-0x65ae5255ea32f755b763805e36251bd1af23e615fe3106aa67c380bc2238d1106b758,0x154e6c6e348282e42d704beac378a3a6cfec71618e3de58afce6e12e6337a6d98a818,-0x3de6e21469ae39761ba26fbb4dbcdedf6bf97d342f019b166123b418f92c690f473b,0x9a95e27c8ffe0af53fc61c63c61bab9121412c6425426c416222ec093905750ff70,-0x148a56de8f117d01a2f17a27943594b97b35742ff8f449c6cc2db9e7a9acb2ee9fc,0x24c1427caba90a58df64cd683975eb28cb2c38b8a8bf97de4eab4f4db2d47a3b70,-0x369c26a3e3cf0e14afb9f087ddd10fcd92df0c596eec77b1366f85cd512add71e,0x42484ae1fd8c8db9cc707ebb6ca41928982b68427644a7b8b570f1a9f318b960,-0x406f3c9c65b611697b0672bc3fab63bd8c9b20d31f94096111dea54c49a6cfc,0x30f856ab837b4a6fe8352500223b2df72d2e14e836a7a2d0a8512c7b21cec0,-0x1c3c617b642931243936210284b445835cc9d0b5525c230845fa3be751987,0xbe49b78a9c4a861d4355532446a1b30d18edc7717b78cb2ce088688f568,-0x37c4224a6c61f7bdca078a84de1e2e1886d8ef1d51a39dd71f8d328e60,0xaa9be1a1d534d21ec8b0da2490a8855c462ae5a1c2df8924687aecf8,-0x137ef353107d1bfc8dfd6cc96474c95ad108e7ec04b1e30efb599e0,0x12c91004ad58dcb53c6624c841dc6f7fe0968169c416128079d48,-0x7db9d4aed21beb0fc7065385c582acc1f38f3f518d4348ca70,0x1044b89499e5d980f18ee50b8c789d1d1dbf8ae60c622058,-0x4d6fd0204fb5f166367c496ee67f29aa21aaa0010bb9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 25 84 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 84 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 58 indices rho q23 m23 23 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 58 indices rho q23 m23 23 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r24 : List ℤ := raw_ints% [-0x137715aed79e1a41d40a786d0b1bb6c9f64613ee2e0029dd000000,-0x1a51c9b73bb595c6deeedfbe8d2accfd3c4b0d44ba032b80580000,-0x10f198e02923e4c785fcbf0ca260e8d95df548f8e53538e99d8000,-0x6e990e07c2c03b0ed2a589ddcf29fa7058026965035481ac41000,-0x201aa78ea3acd14cdd3396e2155a03adb7e770b82f38e1364fc00,-0x70ece05e0b33cf7245cc0ce524d2ad6a573ddf4ea357f884df00,-0x1389eeface4b7f0c6e1478dc8e6b8b9ab3c866c3b1cf68edc9c0,-0x2bac324d28321efc360136f33a464fb7c8427dd197bb8697000,-0x50381a273ab00ed24c8b76b46d2db8adeb142f45c540165970,-0x7a9a32b355e5a6ef400eed15c80e198af6fb57430f4b11d40,-0x9d438fc3d197c5d78ab21fb66ac63e4f4b3869dbe14ba314,-0xaa47a063c49998fefa2f6e092e25006fafcd28a964c6700,-0x9c270b8164b903c2317da4062aa44e384927be6b795f79,-0x796c73f6c1884ed0d48b56ff9112fbc54acef4f391fe1,-0x4ffdf5bedc66321f40538fd9fd7a35e9a3d3c84bc6ee,-0x2c82ddf5a05ddbd76b3f70a8ae4631ce258b694b062,-0x14cead9136d93c89cfa9b357a549c582446720b27f,-0x81a7ef1b6087469208efed57b1c8b4b4d2a8f05e,-0x2990258eada5791e4b4d4070e6b11824dcd8c28,-0xac74c38e70b1110ae5f5b31340cb1572153d0,-0x2347bc4fb233641d2b2a18a80305af524cc7,-0x57b183a89fd7d759781b5abf8cf65fc499,-0x9b92c16a6482d9c45437d144be8763b6,-0xaf82bda34690c671c8460d6f9323b6,-0x5ea4c91b4cdb1de15a5399b38831]
def m24 : List ℤ := raw_ints% [0x0,-0x1c940bed898042f1708f336293c40a2d3f5b63c932b274ccd1834969ff591a89000,0x3597ec2690c1a80ad12e688a7524927c3d0ba81ea740e56006fee0f9570843635c00,-0x30bc8d4a91e8d2c38113f392752295e59b49cb902f9025094421e4cb4b411a3a15c00,0x1ca176d23ce9302c02656bf2798e8303be2a511750c5523b1c2613cbf1691004306c00,-0xc3667f1dabac36db200e884560a2c8b07e9c9b48dc8e200ba05a51b2f7f68ec6473600,0x407e16dfef83629244bd5b979e021cf1a37f33eb0bb96fa9340cdfeed6590778d8daac0,-0x1123b20f70561739b161ee910aad58bd0bd5b7fdda80534c941324bcf87694d4aa3fb400,0x3c4b70c12877f2067bde4cdfadf424d6faf8f18bf1a0999585515ce7e6cea50966460a20,-0xb2f01f8d2ec852a7e91f32e09d32377f65a08bcd57a8448ac28ce562e6bbe119fcbcfe00,0x1c68e41f14e794fb28007592f31406e3bf72a3feaaef7b721f72600487b882a2006c4e550,-0x3e77bfee865cdff02ae9b42fac829261298627a8ab9920a7eadc13028e2efe54210eab780,0x77ee005c8853087d9c408bba7ab4e11b46cffa727591656734c0f22904e18d2cd36059768,-0xca6bf5c8079a041c7b8171dd89213fe4800500fe3730ada4cd70dc95ca33394d4b2823240,0x12dff9939535208ea4422a2930e847782ab2054635dc6bd75e3f49a2f8be7959bb505f26d0,-0x18ff926e6c1663ad74881db4e99b81601233e556d254aa95eb7384ae081b04cc6f063fb840,0x1d7d598dc524009cdb5950e0a70c3a4db919682c40bb29ebd1c00e9d110c722cbc2d0ee704,-0x1f109d1f1825fa9a94e39ff4c37196394f5dfe0e4db764d5d220325720559fd009d2164920,0x1d46d9876a0b2af7eb1f0c0182831a19feb6d99445758bb87eb4fb6ee0678631ae390c0994,-0x18b73d8de51f8d1c4b9ec5fad78cf9d56c33fcbe7183d0ff72fd92dfc786626ebb27532040,0x12b42662db6ac0436309c5553a63ac1790eb712726701b260bdcf0a8322fbe632a15f606d6,-0xcb0a13341db95529cf6f1e01b74ba06ecca8cdeac1b979ca24aded832514bd73b480b8750,0x7b779542bad8715025c4dd84dfb988050bf3eaf4c6af28fc6a750f031b9f80a3a9f7b07f4,-0x433c9a152de086e8487db948abff5e1ff1a59db0f6618eb77359cf1523f33899834d67dd0,0x20bf4ff18238209c1a2f196f3153a7c208ed96e51bdb61e051c25dc16e9bbf8725cd66329,-0xe3d11f8fad425f265e2eb1a6c0de66243c2defa54b41bb4c002a7f10ed11fa4deec18588,0x58387b77f22d58b6cd1c3d4034ab81772436bb2a515b51c8aae4edb52b0860c86ff4bd90,-0x1e563736904428583965eb66e7ee1f4237f108c3307171295dc8fb333400a3e6541077d8,0x93b07baf7b7395e495b8ae854c330c69a245a607dfa311f9b3d19c4423e20b0fb85fbb4,-0x27979335e115d667d17e1cc15f75e6319f21086a5a58aab3a5c62812d0384be4a5b1a48,0x94dc3fb821d9c0df4e3f21b2baba6462c2dcb69b30c033a8f4dbdb4ea6e82db47a3d20,-0x1e7ae4d1086b90e1deb0d3c2dcf771cc6217d223d23cb3368a0e7af024ddf24553afd8,0x56653ba1f61475329cdda55b8fe6747b1dcc43571377542e4572143bb1738feb9eca3,-0xd21f46c1a16a062e6e5a7a74c6fa76863d64105822a01e9b2db3f0d0a02ee602fd70,0x1b234c8bb1b890915cdce7c35ff9ca50b7dd5f1d266e308373294a9dca72f23f68d4,-0x2f18d5b08670fd07d5026159a6965d791621888635cfe8edc50599fe6831ddb6db0,0x43b333d9f091059b28f34626458efa0bb26161e9e63cafa800e6683457a314f3f6,-0x4f46db07f1df0516c4fc1f90548f3155da505658d60c7e25f4c2416914bd7c260,0x4a1e8664c0ae6445f2454d74646e8abd71cc24bf35f5cf30e30200272ce23ef4,-0x35fba892ec8887ab06536dc081f245f96fe123626ae4ca20cc932058cf46a00,0x1db5575c5c85b605e068a9cd041e83b3b5493ac67ac5fc99b493c34d20fe9f,-0xbe358e23d3b6c4b21beaef495e88ba4d3f41a7da82affb40351cc5157e68,0x34ae0550e5e401e5ff028921a2032218fda4d3f9410a1417737393bfab8,-0x9765d32a471468f72635d715f998eab6ff6c4b2850a499435954cce38,0x10242afb088e8c581a6399f06da55d7b3a9d1946164a70e3a8986af8,-0xe660b9424b9d6050e77c350f9eaccb109c626bd68141956e25b48,0x586dc145c21c053abb5b717fd4ff5e56a58b7c36aa35331e668,-0xa64b77e2d71ce9f4f2c1fbb8437ac617f6d8944b9a8a1498,0x2c621f8e411427d836f418cf460a74f2a71b1397fb391]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 25 86 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 86 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 58 indices rho q24 m24 24 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 58 indices rho q24 m24 24 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r25 : List ℤ := raw_ints% [0x3eceef58e7ffddc7825cce5a6cb48ef980ee5cf0f12460281000000,0x54e3d46722e55c0f45dffcc67852afb9862771472b0eb760b380000,0x36a0226b7bc11608e0be51b2d93da72a912ecf457769bc60e438000,0x164642d3607753285caf4dc861a2da7b386ad03123fa6d3caa3d000,0x676667b0589f39dcb3c03a4cda3f662aa8f4116af8634088625c00,0x16b824739ef8105973999032dd2d53e3b66542fe162c004a3d5f00,0x3edbf4cb9c7b55610a9e50d01d28bb22b84a4fba1e89fd77b91c0,0x8c69e55e26e9fae044b5d83bc8fbdda796704a5631886eb70540,0x101be40cff809740dcd5d3700831f753e8463c390ac1eba54d30,0x189a30729aa072da9d366e1ca2fe528ba4b811083034f83bb90,0x1f888c176abc7a6f9e565f4828cb0cd5a09106ab7b9d8e1b24,0x221d688261ba752a30a57a69b3cac305f07cf7d48b62691bc,0x1f41ad0a741c25b7d1dbea47dacb9f762c5975302a7f183d,0x1848124f5dcbd62beb6a5b10e557cc7445303a15e05dd20,0xffac8e396e028574f15a79467d2bfb8368645f7d3e3c5,0x8e1bb58c15934b6b290225f364ad5e782fea19787af4,0x425961be22cc3a8b059c5d0f2789cef2a815ddae3c1,0x19ce3e7139d1bab70c2b490b3f5e0497044144eaf0,0x842aa7161df869e964fe0524bac149e8aeac80aa,0x223878ab927f40eb676305f13ee63a4bb6c38e4,0x6fd153046d603c56e1fe440a7d67bce86fec3,0x115692e4fe7e5896866e0c9528800e8f07a0,0x1eb1e2677a458c3d95c1c3f7cf251bc1f5,0x228c80da44d6e8b7d73d52e359341aec,0x129532c9b60c95d55df764c59b28c7]
def m25 : List ℤ := raw_ints% [0x0,0x3af15899eb988a11f82759fb50c454fd52ac7dcef89010e6701ec76a9ea7c6ba9000,-0x6dd694686b04f64b888e1a194f7e94ea2cb80abf38f5d9160e6db00243810afcedc00,0x633b94dfba956795285b544db56f6c5b64564ba24c7e1f5b5b07315fbcb1034cea0400,-0x39e70c6e6110e1197553b67c0a2dc75ab7d81c9fb1897c22af4f8e32a36310e37b26200,0x1886ce05b1c42bdff49b2bb6500cb6ebf5148bc1066d3c04be6ac47c9c59bfd84d62e600,-0x8096c0f0838c81d82b225f216b2a05184edef173b608caf5c54cb21a93cbb2e01c19f240,0x21eb448333c722ac6c5fe4bb9cbe310449af99f6b7108af9744f78b1af80e34d479562000,-0x76672bf6d977bd9471d9133db2ffd56883566f0c6772e4a1ceb70d46a78dad387a29d6aa0,0x15c9427a21c3e928faef356c01b327716460d3372e349133b1ef830d126df0957fd558b600,-0x36e276488862f80c4ac5d833fedddb19bb58d343da0a551464bec7bb1b16dff8be60943c30,0x77a49fbaeae5461a0002cc5b4a881e3074a52d67f87163b3698772974b5c37a6e1ae2f1c80,-0xe3a575cf4d5a83cb44a17ed6310142b9a4954927dd1c8b7c90edddf5889612ee91114bbb08,0x17ca9517d0f1186fd30ea2ec03d1600f90b8c9ccdb39e62d3f6051f4f8278fdc9a405145840,-0x2326e7e8a3c3bbcf34b7348c56d5da193000b717a0d51780a6bb0df4d713d5cdca0e66f2f30,0x2e166cc4a82237a16d90a79f705a84727039cf00cd5fb065e386fe58e1cc71a72253a985f40,-0x35cc36841e46662a11392c79edb3dcfc27cc812e8146aa57383b99d5d168ac7af52020803a4,0x380d1f252c661f5f9d5ea3394ab82982bfc2ef2c89ca502b12efccd6442332eb2b1d3e33120,-0x343897c0d4100c5286c3a60b48b17e896e287f49d03bb0c8d9d6466e7f55f0881e28cf795cc,0x2b8f0825b0cf875c0d4055520495ffd17afa60f94e22bbcbf791b1c94c4d284e04c78e1e580,-0x208cf91972dc17fe5f8e8b9a586afb296c4c58f75e126c4618a769c5d3fae33bc0b3304943e,0x15cb8b4196d03d26303c7492c614585c9a7f14b7f86d45ffe87578d2c888c1972fc73d012d0,-0xd122f6444364af2c225e84fee20a2455e588d7d005d9a775b886699c7ef723e89e88d8812c,0x703e007a02a5c6a7ba2f077a6a998ab3187070f229e6720f898d3084567cca8a765a82ea90,-0x35d5a6271b6de6895d7268f296e267a17e4605395cb12cb9c5dbddeeaa13a9a0e2d5111831,0x1708157ef5655bb87cb4d1936785032d01d8899f34bf03a0fec6be94096ff875b3bd65b788,-0x8c48619fcbb02e55e433771b36e57e67304953cedb8a0e989d216beddabdd4d27b0ba9268,0x2f5ff5a8a460bc2cfd085b0edf3e00ea64a1b5adbaece778405fe3081404d8580ad93cc18,-0xe24163bce0802d21712761a7407295d10e5a6dacdbe4af015b5ed0f9a4311d4d503cd5bc,0x3b6e41370da21a8b2199b34198aadd85e94323702a9bfb68459190bd7065fafb1f004fc8,-0xdaa81e6a5f02269bd6561b0a04f7a8789d771ef90e671ab4e2be91ebdf08d7b5b5db678,0x2bbf4a418970d6c1133949c8aa951f3893d1c6d436158716cacbc7db8fef39c51418398,-0x78f85d4edcd4badaa4384ac2549be3ae31a511704d6e63206fa7dc58649adadb1b2f4b,0x11e81ed5b2130862074f4be14fc8a15b91e13b89d79b23b21587f6e5fafc4dc2dff570,-0x23f66fe4fd0d6e326eadbe6b5ec04c7a0419f3788f02b3e68e03b38b2e548bfb28c7c,0x3c8599e1085c3b37c777201b8ea637744b213459347b253a89b9f9a2488a9b83f970,-0x5426eca908e715f42c244cab43f3a78cd39489a8c34b45f4b2c5433cb1e02cc55ae,0x5f0cf99fbfe4ffd42b95d9649844a2a14f9b05c679f7c09b71e4129f34db6f38e0,-0x557228f29f5a419dbf42500a8aaa7002f359c342c8e62d5205b7bba2ac75b1d1c,0x3b9f244a81d6394ceb29eebe3b664e163910ac9b53c50dc0b41c53cdab332c40,-0x1f4e7c283991727d85e89aae9a59cb307f96b412954a40aa34b9c4f7e7f7bb7,0xbe5cc783d40bab20ebc61fe9acb86edf9f639eef26e0ab030f0e71a63b468,-0x31ceb0fbb345f66cb27c7df7032c271dc9d0f3f68d61c10bee3e8356fd20,0x866bb87183ece50cbc8479e8785605a263819c755f92558bf651768bf8,-0xd5decd06ef3cc4e0ca86447a7af70c9368c40a1d88fb5e3ce4586630,0xb093cdc3eecc40e552aedf88105efffd77fee75946634454e94dc8,-0x3e2f888d87b09e254b4d1452835529577211fa2590c7a13467d0,0x6a37bf48698a6d73fc4cccabd7a790308abfb2af3d3d08ed8,-0x196f1f2b9592e433b413db5473440b7345d888a65ce3a9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 25 88 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 88 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 58 indices rho q25 m25 25 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 58 indices rho q25 m25 25 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r26 : List ℤ := raw_ints% [-0xc55044dffcf61b5bba323f413a09b4c0fd665214b4465423f7000000,-0x10a94695097465c82df8adca9aaadc4129d0c5be97c78b92121080000,-0xab781b146116e928188f93c76d8bcf3d4f26b67d8d2b5d2f9a108000,-0x45e36a0f50b9c114bb87e33802334de2dd10688b7646c8b3b438b000,-0x14446202bd7a63fb97218e847e9851caa490d42027c5269c45b06400,-0x4736cefc95ec8c516d487e1c57d69e2a261ca5e517c124cf7f3f100,-0xc4ed24c28ba89105f35c44caab3a02b1e5b39d524d76dbc5528a40,-0x1b7a266adf961110838b0b474d5c74c9d8df0189e164973146a740,-0x3267d5ad76b25a869fb3e92757a31a649ec5a0db3362fec33cc10,-0x4cee2522d1d0a15ed4975c6b76ac791b59762e840017f07c75d0,-0x628862bfaa3c1c73f8d0b33cdf1c1cac570452641d7a0ed22ec,-0x6a845fd6bf1bd0503bde26ae39b3f9e034db91f28adacb918c,-0x6182ff32fd59ec3018074e1b06792975577b66f7fd1ee259f,-0x4baf1f7076458dbfc51d0519f158b94d9f8133c05c527ce2,-0x31c27a375d1bbe7c41cbf74b4bdc62f6bbd1896a900f10a,-0x1ba0edad110c01209a449dae63f7c4dc2a59a0b58b7049,-0xce295cf18b51c15e4d19e6d9e4843876810013748f51,-0x50161c79f58e7b37a4e8f61cedfb153b9d41e58b0d8,-0x199a159480b64f950aea19daefa2ea71e7b38c6fc8,-0x69e8beacbce87ec40fe31811eb59d87836afcfea,-0x1598597415666d94cc1c551e03118d85ceab771,-0x357be65551a51a25444f2d0f55ad2ad24d31e,-0x5e82116293272c13ed57ad349222c853062,-0x6a278089d40a7d771eb2e24ed54c44f59,-0x38f784d6580e68eba7706c5e5fe852f]
def m26 : List ℤ := raw_ints% [0x0,-0x7991c6bd75ea9cc50fd129965694ef4a7a83c37ae0a922db473f7b4be73a09e0c9000,0xe1250cc91da553663be1dacbafbb60b6d9db962a657b0fbd7dc23b04ab3a26a9aa5c00,-0xca1c4552ec1723cf70ab28838e864f4645b5161403e7796d64d95436910ae5658b25c00,0x7527d4c36d1fa453f431301fd711d4533fe8fd0184711f5a833a7de9ff48e99d2f18ec00,-0x31498ff136e797646ac9be7684163af020786350d47684de2c3561ab6ff52b1ea7e9b0600,0x10095b3a7ecfb858084a7c785a83a58518578e999dd20018663f255519feb853b2a8fa26c0,-0x43300ddab47832ed743af34afcc883af97dd80ecc7d0dc1b5c64c31ee6f1941c8567e00400,0xe8c321d07749e45749f343d81320f68a2da8b99643c49717892dc736557770f32a0cc77520,-0x2a7e0c8c6054d7328c994e0cfca98aefda6b3c0a0b8dd5b3caf54c7bb3d39c3b1f1f1514600,0x6a2d5b946d3b349cf01c8e6baf67ee40f279843e5870aad5b8382371fb91cf738e0cd4bdb50,-0xe57fb83264a28b49e60b8f459a45755249189e466377f8da04080d13714b690566321275f80,0x1b0d525056c96446f692929b4472437e2f6d994f55582bd1249e556c57190b9e8460b2723928,-0x2cd25e2265f9ed76de73c633d0562ef6b5ffb53f456978afd77e13f211dab31869c895424440,0x4198160d7b3aa641f9df49a57e8414c630510f2cdcc47bcaa8ccb1416ee31e756275be9b4950,-0x552589191e416515403a654f44ed80dc3cb0c00b2a14cc53372fe115b9539267dde3bed33a40,0x625ca6d125e7255f722619af13d6a0c798f5048cd59e79e0ae7d114439e8522298cb8170e244,-0x655fc2141dbaa4aea34f66c46fee11af4d561cb286f4c439b50c65d52d4c4448e8815c486520,0x5d610910e8658958710d626be4e969f4d5dfd6b9c19ea8d51d3fea5ad5ea02852bce9eb66d94,-0x4cf7c38bfa0b1a165d8377ceefd362d9bca79c0feea222882ef8aee396d85e0a92c8cf85f440,0x38cdb4e0fdafe4b80db5ff2baaaa6fa72dce0b8a77ba3fb3e5cc9202bb57d5fd0590c7d7b0c6,-0x258a1451ae5563db7aad61599c3571626dca168b557bbe1670e68307994ebe990bb03cfe01d0,0x16349ebdf05e19b8edffc3c748093bd09df27f62aa03e620bade8c210f189cc56312e36cda14,-0xbbf07504f1932f29ff95a482b2433802ec7f2d736a0d0a089e64c5663e16fab81b0c6254450,0x58c685ddfbca6c4105a82b7d3abcdb39902989a6f22d9d3e8a7798e3f196d2c723156b7d8b9,-0x255f77877f71232ca9558da3ae0398540fe3427d38d1a1ea0fa7cd70b4eae3421db8036d488,0xdfc9cc15a6e3c5a6ecfac5666af7cae658a418515681e8631bc78e92192f980b76545dffd0,-0x4a393e05c56b6c6c8cf96667ba42b11b30c400839184f1d64c584204e7daba51b7cda682d8,0x15bc1787198abee406de0abee4d1dbe8eda9c0f659e1ac98370aed7d11195a588dc4283624,-0x5980e5c5c7fd5a0b6d7bf4b7fc03c0483ae7a02d11e942468a07defb695cb2a05b56169c8,0x1423ae26cfebc7bc3457d9d912463dc877c75553d54b39a9eadc4c3c5b50bb3b26f3e4b00,-0x3efe029e728ab101065a0148456f860b0a039a1323c5ee97df44a6411ccbf1b11a533758,0xa9eaec6d6009935d2971caffc9467ee2bbea82838d1f267c046d7a838cf90761a7f9b33,-0x187dc60f7bb8ad716ac88d5c5dd776e9a76745ea0c3db72c5e985b9090e2aa0edbff370,0x2fcc24e193170e6e992a810602be883c7ed30dc8780620d873d571c3b1f4b97a202054,-0x4dfd820cdd8b03ad315652875ab4d052f70b675fe914755c4ba481a834a0fd03d13b0,0x68dfa50e3c36396afe7346109888363dd9eddfa3c8cfd86f24020729ff15a63b8546,-0x723ba34f85f58fd0c4c9fb657b2cf98054357ee442ab58884fe1061f5a59a574be0,0x62b5fdcb13039dc66205bf8fe03a4f734ab29904ca96c0264f8022a46249bfa0d4,-0x41f7eb0f68001a442fca53f2ac557da1590945ba51dc2ad2a21f87df4ad786f80,0x210a372ff62e00f0b9b7187381ba4228dc1c44a720e0692f4217bdf30b412dcf,-0xbebc22282a7515bcc92fac239ec56842b5e64b269dd9db37d79d1a79e2e568,0x2f2132085a458cee8edb73e09a3839fda191b8f2c7b691790f4044e5a52f8,-0x7767ab67a6a2147064cf04f82c1bb4e039983ed691cf31f7c9561fcf138,0xb124f0ab05df87f86cd67877c32182dd1a28d4e67e16495085ef4db88,-0x875642a887f35f01c9e70726a4b59cd3895cf2a966934d97a2c15c8,0x2bb9316b9bcdae6c7d8592bda606898e2f8ef488735504eff5a08,-0x43d483538d890c07880b85a4e474b8a34b3bb9a154b15b9f18,0xe92972044d1910bc4ca4d638fece82a88dca119a8ef201]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 25 90 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 90 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 58 indices rho q26 m26 26 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 58 indices rho q26 m26 26 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r27 : List ℤ := raw_ints% [0x25ce0d5d651c385d75926b6b79dff7189356b2bd4c0d94c158df000000,0x330eb9cf67d9f1d4fb33601acfe702c7a6bcb6e2b6333a990e9dc80000,0x20d41083cf748380d957e8dfb6aa4ca2808962e7c21a608f06892c8000,0xd5ff2ffe875b6431d44140401acf1f1f6600bd867b2dc364f5e9c3000,0x3e07ac5891c7ccb7ebf366aec99f97ca2f68dfcc1efd1e4c8942d6400,0xd9db17bcc54cc5970bd95da244ff56d52f8e19d874eb20f8e1186100,0x25a1fef791ab6951bf9ad1d57bdc09781933db16b83403809b362640,0x53f8096dec3e314dc843f258ab3a412b186e68f6513001530db46c0,0x99f29b3593ef42d3c61ddb71527e306c8216585951f64bb0bc9d90,0xeacffe208b0d67c88345ba702cf25290d937a2d25d720d140fef0,0x12c8c7a149afe9cd320d2a32fa7d48c637c913cc1538f3965434c,0x144aba3f1b2d328ed6ff77f56a107fcb4aa24542600a440f6644,0x128fe45fa265fa2e901558c224d69e319033ab382ec5c97a517,0xe652767d137d928a04f0b2ffa75ef07168127fd0320d3ca28,0x974b59cac831af49fb4a0127a0feaa5823f3f7d21af73fb8,0x53eca734b99230fda3112923316f9480124816b7b01f7d4,0x27196486f63a3d831f40a5d3109f72948d6c4d4a86a9b4,0xf2bf20200c5a09592d06fa37f0efdee2e978f1abc1e0,0x4d81c7b7daed552a7567186d6d8905a06bde4ee9920,0x1403517341d2223a4a2dd3c909ab8cb9b1bc7db3ac,0x41329e425e0828b197ab586f2dff1c9315a1c5a3,0xa138c52f60c50d466c2a908442c2e3ac4427c8,0x11c663c94da5ca140f00b81947f854be27594,0x13ed972408e8764c4599375cdac268183bc,0xaac1ae1be8b0fb427aeabeeb5632d20a]
def m27 : List ℤ := raw_ints% [0x0,0xfabca9e6c333e356709f65c612932d899cafc32d6f5cd7e442f2ee4c8ce7b45f9e9000,-0x1cd915fc24efb2ad7bffb5d3311ff12a0dc94e5b7714dd076d36099b9a127efbdef5dc00,0x19bc4d243a36755bcd680cf71a7cca0ca58af18127ff1e66782a3928cb1243965d1710400,-0xed26ad42dfda8ce2915f33a6a0ad6eb13ce3058fe22d84e229dcdd1b0babd075b34656200,0x631aebdda1ba65a235d124459589c965724da4310a90cd8affefbf02f2b8efbe89817f7600,-0x2005f7d88d3e3ee9cac46630d532e5c0b5f506a727541c1ccef1a8efb60e2122f9483675e40,0x853535e71a71a0de8bd18d00b4aa45b178af5ea5152c331291fe1f3adee611a25b6901ff000,-0x1ca0ef277d59cd9bf763824e58215c89cadb5fa61b980b3a965e2029e81bc1a9f6de7646d9a0,0x52fa72d9e7c58d363ff19633b05e827d184915df43fb1aa0990b9bb3bf79c635f72fa5c5de00,-0xcdaefc22bbca50bac981a180b0e095154218f05e60688dc690fb2f02f2a7e6695042fc53a630,0x1b8e28df6651f585087c2310e13e35482e8c0b8ccfec6774bad234b04b4d1e875c6101a67c480,-0x33850f951a7886d0ab340506ddf84d05708e36e714524e25106b940c7cc292950d4e0c3ce91c8,0x5497dc3d3d0747857e108a6eff5898fc8a2a7f9e29be1fc6946c4dd5483acb26cc62df7492240,-0x7aa2c5e93cdd46c6922a6bd38891909520cf315e8ab609547b962f597083c4d7588ad22a1b8b0,0x9da226ae30e9f3ce6b51e38190d4b6487ab557eb7fa61435085b7ccd495a58265e9e077943140,-0xb43ce00ea8a3ba1cc413c6d11008e435911d3fcf16e48fd21d3fb9b9f8b9664db2e38e4074ee4,0xb7c5bc1daa11ecd1419cfec394e41ad8742d6af1c2fe359c40c4e72f60553a5200fcc747d9d20,-0xa762d850aac20cd4eef254cd22388350c2e5f1fb74245f61c301093db2f5265ec901501c5edcc,0x885a1dd68e627cc61146d16f6f420f9f6eb3360f4e4b3ac013cd0c5692ba0b78127e31f046980,-0x6364bf0f845a00519bccba461cd0a1185e3e2de8a05d45b2489f6c012fc40d1c6a6264adfa26e,0x40d67d8fead86d39cfce77593a26be8fe5ae07c039781c5bd8fefea6f2ecfa086859d913b6350,-0x25d533bbedd07c0f0e87e1dc0974f3e11747a05c034dcd07b99e1f0b662597cb3c589d57e700c,0x13ba050a0a0cf4a83af0a0f5ac726262b3a54db4ba72010e38076b22f2b647b42c2f49f55b510,-0x92d7c1935f45c13acc92f60164a3b3e65e0ec077a98be18fd18870343681dc7ef9dd7bd7d3c1,0x3cd58342cb3605230474611d3aaa825c1c22c21c7a813d6629ec864ee13cde28d1761f649a88,-0x1662319125e563b1a4050557b78fbdfcf53efbdf8a3c871f9dfa70506e79c2fe059e26cc0328,0x74a998120b961fb6d532e9a45eee5a193cde3d7a051d51f7b61a6b838c24bd287796c5e0718,-0x2183b8304e6035b27b4b58fcbb2c1397aa76f154d414e0b5e75e4475f7e792857d590d4b5ec,0x873ae3b609dceafee18a791693a4b60feee6c844570e6f8c4153f70bbb0d93987fe30c5148,-0x1dc643cc2604aba98288386c5c77a63fe25f91d0af287399b4c305339aee6267af8fa8ba98,0x5afdbc4c103e2ac5482049bfa29cad4c1c4867251a5d8bd77f97151dc1f372bb813872f18,-0xef693bf41b1dd5f52e5a70e7faab003658ff0c18a5a2076f360294afaf6d801986a3c05b,0x21990849a087dab1fc4bd978c54212e9783b8ac7b576224cf3fbe73148df7ca66e597370,-0x3fb5a685dbf73be9e900e0d0c5ab48882b36ccdfde2d5b999b5205e76c16f51a20c26fc,0x64c5f8d70d1347445826ce2fdf186437fd4f5bec6ec4d9a9d526971a4b1bd700424f70,-0x8306e1a073c11c8e7035313a6fc2316f7e64334e491c83af7319763d9795aa9d172be,0x8999ca50617eb61372fef59f4f26b1646efc01f067a8ecc86e05c08ce3934aefbc60,-0x724429b8a62aebfc59745b832c3a1f2abc7f81164c60eed642278dd1b10ec2a883c,0x491e09b1c0385a35a51349dbe0e24ecce3537c8775582a53cf559381905fa97dc0,-0x22eb2621402e8ffbd1d5da87a64eeda89abad044a5d2b245194c077c805b543e7,0xbf50ac9b9a9751b3a981ed103a6437805b2166b04702725eb15cf7075de8f68,-0x2ca120526516b123899173f14e20d89b563255c4d7ee901dd36b396ad5d3e0,0x6a1ce6b910e241cb922ce33fd1b1a9831a95e3d5a03d4957016ddca11ef8,-0x92bfc17c236d0fcc4ed732b6a9fef8b18479a8bfbf4fbfcd97a4b9d400,0x67b94b7f204359b4cb9cde028339d13f8fd19e001a2cf714e0c14e48,-0x1ebcb318e5ef5d6ee29ce5bcde431f2f1b842de00eff8060e77030,0x2b4e8c9ec58780c2894511d9e0fc131eaa5948429b608e6d558,-0x8591b2dd69c5c7e336e5b113d5d6d59cb8587d21f8dc499]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 25 92 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 92 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 58 indices rho q27 m27 27 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 58 indices rho q27 m27 27 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r28 : List ℤ := raw_ints% [-0x7151af2a583663171839b1e17451428163270ba8430b1a81f032a000000,-0x98fdb08dc1123e3a10a7a9811294555b7a98a25e1932c9363ccea300000,-0x6255165d9ee6c34cca5415b74d61e225684a36488c401331e27d2bb0000,-0x280be8d94487613e0a5da204201a966019c2d5f411cba5bb211a3aaa000,-0xb9a6ba9ec25f0ac226edb620ace2abb460bd13a67043f65e0a6ea98800,-0x28bbc9bc6f53f321a0e4a07a5d8278c431387ac8d24ab67a29ae338a00,-0x7087543aa7cee3c0688ff543e4f8bbb86c9ae9395b10d9ad06b8d9e80,-0xfaf44178e96af1249c5fb6f208268b3812d953ac99b581d01959cfc0,-0x1cbd8ca323ea59400cfd39ef655d2e4c81fa543f8ea31e64128ea320,-0x2bcfc3e99ed81375fef6f7481af68308cc5b31be9cc733dc42cd470,-0x380ab84ad855e93efeeb4859810d5061dc433c705c3ce48bee6978,-0x3c7fda5d9e445a9c4801d3fbaaee5b55ae8204cd5066909ec86d4,-0x374d718cf9f444243e0ffa603108efd2a133ec5913ffe53b2bbe,-0x2adade34f685d3dad00eeb808e75565c5e76031a31090f55603,-0x1c20a06edc8af1b2ac0b051f12913aaab57cbd5d9476e6ab14,-0xf96b80b097377d3625beb29a4d9cc4ca265cfe315dff835c,-0x74171d712eb4e6f81b6fbbf18c64b8e340b6467106c63ea,-0x2d00096de8b36387f1c4758a9544c9eef9343101a8f082,-0xe5a2887fcf5a1200bc7f7521e772482c5c97825f9970,-0x3b38e6326b24a877af8d244aa139243acb6eba0f2d8,-0xc0ae3c34e736c10f504003260cee975ea093f4672,-0x1dbc928ee6ddaab9bc26c387ae90e8bb7ae30943,-0x345ff853562cee8928e00aaca8e19e543f5784,-0x3a9ea8ee1208b4db51e382453c38f6efc500,-0x1f55bfceadab8e82fc7ff3baf39fb73ac6]
def m28 : List ℤ := raw_ints% [0x0,-0x205251e6bf29b04e24848c1e8864f8debd32a828db5af7d46ca150b7de29de4053709000,0x3b265c047c6926606c4e9841744374cbb3d7319ca59b07df513f73d0edc625e77bdb15c00,-0x34729f9cc2b787db1a6f98d6cd41f17c481cced10042d9b61e48dd2acb6f65ae67eb835c00,0x1e043ac8624abd07d58348b8fcc89491616181c50e755367a8d201acb013ed7f7ede4c16c00,-0xc7652ee4ae66999463559c04a6a2f01c558b168eecec229ff7e86aca34744a8366645e95600,0x3ffea423ba71944e72089e808f513f9aad2d30d811845c3abdf0098f27bca3a4fb31fa2802c0,-0x108561071891bd0d440e63b830480de8bd1b3593064ace58465b9ec192ee1ba3b9869472cd400,0x3865c6262b758478fada9e95d26b324c2898a003879cf451ae56fd49eaa4783310ffb572ff820,-0xa23b1465e997b08d6ec632642f1532f61c89d0badc4a69e8e7642ae8c7902fd09f43db4964e00,0x18ef9cb8581b4fe4babbc232025feb858c63616e9813dc1ee8e97c07cec47e2bea1caa538be150,-0x35039e14a452404a214636ea02eed4caf956e5041c177122dea471dc1bfca3fb0fd512129ec780,0x6246e7b09b481373dcd32e290c772b9d7ed987c41e31e62ef0bfb4a86e312baf86e749a577b0e8,-0x9fefbc661f0c2e17d1c036af785ff4cf2050b634b8f9c8134b2ee4c10d6808f848aea1d5722640,0xe5b7e8d4815d3f1570c1da117c39a272057d91e236fca0c3fead3d9f11616ba48cceb6e19197d0,-0x1246cafe5290bab567855974bedec5be0c2078fa74ae20e67920a5bc85384095c34850286e9cc40,0x14afbea7a4592afbb9088eb6d852a0e414351b8c50c54815072dcfe132ad3473a0f8ea1d71fbd84,-0x14de971d2b289f115c554ae634ef903d622e48eac71510f01a7166e4e5b2a98f196e15762167120,0x12cc6516c7a619bee169b0a586b675c143184a91dc4e3dc426bbe208cdc7e77a453b89c6bfcc194,-0xf22b0e571d7d293e82484b29594d8987099272790fd3ac192627fd88055cc99fe58c8578a79840,0xae60de3f04efb873d5a3d8367a61a72ab0aea7069a2acbb579a77d850faa154ac9369a41ef6236,-0x704bfbb943bad4b715ee7f27545f4aba915c98ec90336a598c24a45d22d58fac713a6b5e09e050,0x40a45b937c78700b932be6fbd5fc66fdb6b3c54887595126fd1cc88fd48bc01a2b273ace563334,-0x2139ff554a8d4594f989a57f70395e8bec59affb72dfbec334c9a9adbac2691e9c3ea0b63ffed0,0xf3a003542be159a40f209ced9152663f426c282547c033ce88019295e46ec463a66437322d249,-0x635414f180aa766582447de7f7fd1c44e54818e9c607b7d11ae6c228c2c2b37b7243efc59cf88,0x23eeff2922cb6785cf6aed007b460cf20fee358ee34d77cc6833fd0726e507180b715de852610,-0xb7f2a2cdaf94b6237fef9e2db18485c0ebfad711ba927f0b964d352454c5d80ed7df752891d8,0x33d7ead9723b4519a4cb8bdf30b9879745199dc9809c75747a4c3d7eb90a4659cd6263d5c314,-0xccf7f3199c0c5e8b0679e7594010f8312e75560c7047ec629b67189f8b88de44ef7330ed148,0x2c288a27d52db7bec0502fc930283ded1ea4d25706080f7df6160dc73ec4c8112dd028e1fe0,-0x83d82b3851df5306a7fb8ec6cf3bb4662f6f695ede88dd5414d9082423f266c6be435f0ed8,0x1525a0f9619c74a329c398f3f1d1282500bf5e11e882a5f1d438eaeba4bc79273299d012c3,-0x2e39ca088cfdb5039e2f5ba7e9136a9fcb840e5a872674f289fde719b81fb27cd0bda7170,0x552846ad16fae02544952d7b6aa9b4603c027d652eefd402dfad62bf7fac3c909d0b17d4,-0x828e55f161de89f4bfb6dfb41141cf0fde31fd26d3f08e4c514e9d8b4dcbde6d6cb91b0,0xa41a35cc7b3d7b25302dfe0fbe3701b532f5879d68bdce40471ee9a8261add5d926b16,-0xa61d92996c49207c44f2075560e10a7d025d4fde57f1d989efe30be17624405922960,0x8487e2fc0185e674f59d8383050a05ac492c14695f4a2d828c80b725d8a6fb3a27b4,-0x512ce1bc689c76d8456ff874b26dde96d0eb5d63ab9b2824c15aa69f0d0954b4900,0x24f420fd21b0b9a31b6f9ac890b83122616128cba359e5ee4a9037a7571698c6ff,-0xc017bc4bd0ae3274bc197ac33947228897244dfd8f4f410dee7b98a1bad22868,0x2a4a8d9d17de2c5257868f04348c904e31685c206c63331e48a6422f85ba738,-0x5e567c5281a71cda7490d3e874266d8594937828e687f88d942746239e838,0x7995fbe1f6a8f373d9e6a86a1113ece78f6741dfb72e7f8594f98d8f798,-0x4f7d93deda2973655676fb97f5fb7c8206ab9018edbad8aedd915f048,0x159aa65440c35802fc94b7e8aafc6bffe683799e8cbf8f5af74aea8,-0x1ba4d8adf4c36678cac03e470a3af6f972f17356bd90e3474198,0x4c80f65eaa3e4243ebafaf0cdb39470dba6421955cc85171]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 25 94 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 94 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 58 indices rho q28 m28 28 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 58 indices rho q28 m28 28 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [-0x1f55bfceadab8e82fc7ff3baf39fb73ac6,0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r29 : List ℤ := raw_ints% [0x14cb780407a0986e487823b24e2116b552828ec0d7397bbb5c4faa6000000,0x1c10d7d007f5700ade895691d38024cd866fcbebd4d59dbbcf73d52500000,0x120858e48041a69b0206342adc7c311d2557181d8f7d2106a5b6b15250000,0x757592fb88a00be5162991e345fd89834fe712e8a768e80c2b3e5f0ee000,0x22050ab8ff42e3d97121b98133839355576a7b1b56495e1af65ae9a36800,0x7760b1648737c318d3ee826925e6ab36ed5e61dd89dc0b62ec4a5767a00,0x149a3f0d76290097e539a602a71558c324c3ec4f6a1dc610824eec9d280,0x2decb08074605d21201c9ecec534156556311c01cbdd34b21e9b659b80,0x541bf1223eb821c8986dc15fff43623292fe4098b61e6e8ffd61ced60,0x80253afe2e10702979fe367204f879e8be731ea8f61ac5033251fae0,0xa3d2ab6c4897312a435c3a062178be54933d28ffcf06b79671b4868,0xb0be572f16f4b44cde5aec4b1621a18a71a1207015a81e2f3dc568,0xa1742b0142287c45949b0d073fd912fe095865a851d26957029ba,0x7d063e2cd682510d5f150fb3c2b6f6200b1153636fd963e00278,0x51feef67f62d8b37d4f66ada592f7ab57efa5ac910ca5dc09a1,0x2d680146c835ccd5824c5d88ccead7c9ba9547823abace6378,0x151d82d0853c26ac9627089d5e02a809da0dd8c4b77a57c56,0x82d5912705bfff5f5e9e22179e649a8b69f89ecab3aa710,0x29af5ad9589ca70f412293cc5238558963cd93a44832ae,0xabd10906ec1b3eed7e6103ede9484d585c8d846b7058,0x22e5651c965dea441add1be3b9591a248397b89597a,0x560e80c407afe4a5e8a6a2c00269167cffd4e9158,0x975b46cdf8f981239212c5e3b2ec95c450bb0d1,0xa9246e515ce4bd493ddf5ad8a77debcff5b88,0x5a4316cc8201e674deee491296593d3c30e]
def m29 : List ℤ := raw_ints% [0x0,0x42a9c8ebea45fba12b5160fef950414b66387ad4446b9f26200cb67b3a365a64ac1829000,-0x794c5b22210e6adc18807c82bdae47ae11bbd653158fc03c9792dedeea68ae2d6f73dcdc00,0x6aeabb67c5a7f44d97f1e05d3f9e03f534e0e630e236ec5cfef2ba412a3f9aa3c1aee380400,-0x3cd071fe1c7fca1065763ff36564f639300cebb9b34636c780c5b2e3da00932bc582cf386200,0x19168916467830446a09360695f5ff6837bb96ae4b0ed72cf699c676b017c1f074b7df47c8600,-0x7ffa9a06d505173fc1f8dedee33b31978e494555748e23b92ab51caf4cd5a7602290a4e44aa40,0x20d015cafb83972335159c87fea1f63cf20c4263cd3e235eb37a5101d64c96c6ab2b39210e4000,-0x6f370a05f8979566b8c0ed89b47da0a6e7a4204eaec9bf98459c35a65ec92cd7277d20506780a0,0x13d8c28159c78f270af510a8f1db79f4c514b6509b837e6846a51baefd1b110ef2c28167032c600,-0x306ee541a0d10f6af6ede135e714059e0e0e50a94621218c112f744cca3adcce0276fe5a4cb4030,0x6624accbdd6ee0179d1709f62a4596d4d5e7be974a0b7fbd85ed424c47346fdb369a7f4568f2c80,-0xbbc4c2652383c4cdcfb34c45a8a3260e7fbf57bcd4cc04a893cb674e69205c92009d26fe1796688,0x12ee8f3e8ff288021bc129bc51df2c52a2c94eab55d6ca4b18c0b6499bced0b8e0df1fdc675b7c40,-0x1af1c1cdebc29cec530a46ad20a3f71ef2d9acdc23daec753345fed68f78df97886372d54f329630,0x21f90b040f05afcaa275dc1967eb42c1c09842a810df96c2cd723df413cafa5fba80c95917e01340,-0x2611cc5a2b97842a35cd2eaae55f44c1f9d8abed304787154a07915e0803bef45c9a629f029eca24,0x260170c285c930aefe965ae455bac11ec5b58b5c4ddd8dca93a62f9a81e5010ea06aa76aa9697920,-0x21dc090e31ab69e2ba96908504840729dbeda04970a7a6f6edd058dbff6d6799e0af2a9e129ae5cc,0x1af2eae38099798bf00890bd5db53d6fa08cc7a092e5ad29165be9e59349f54809978afe4587bd80,-0x132bc334e7137128f7740fa07c2828e9cb2460b4ec42f3c86ee6eec9a65353b9b60f6d9b2714ca1e,0xc30612c5b1a869456d44ab26d9253709058a700704ee1a7aa7b6c7c9606b48a533b0be29e60c7d0,-0x6ec29a3c1a3d0487436fe6984aae3a0a7d54b8dc4c4e13fc65a463567b4206e6808d16da5fff7ec,0x3820ae8fba43a1e133802519ed73075d9a92fb2233c173f15d9eed3fec78f699405f1003e66b390,-0x195663e057c77deb50a9c03470addb57223744c35b9b99ac500952e36e7754ee5df039e8b490751,0xa2acac3e3b739f10ed3be9bedd9118e911eee3e0ed24c5474458471e21922139d203fea0f38988,-0x39dd494784f2606ae9d8480712153f6e21b9da49d3581f15b2f7fb5304dc7a5dc58ef4eda4a3e8,0x122f21880cd2cde87a7b0e951adafd158fbfc63bde9c69edd333be856e3806c19b1fc27dcbc618,-0x5072aa12be42ac8df77f074656e3eabfd5c6231c0ee14e70a833c54fc2f08bcd48f5945eafe9c,0x137a50e0df23a6a33450bd65cfc1cfbf2f46e29849574b1d1ebf957a7275e1d85316f91ed3ac8,-0x41b1c96baa11add1ddbb256e779729317b92e1691c61dc065713c999778647050ba02a991bb8,0xbf9fb53e7c7cd07d97da2cc46b0ff30ed49586ed639ebb34ce15a58bec0207ad41a04a1ea98,-0x1df9b37d4d3d5372b1555b99088f80161741a3f6f2af4f4f98dae84ab51473c598d21d7fa6b,0x3fc8672f9072657fc52320f45e59c3fd4e61561f7c23f24c9d08ce9573e9d7f8180ef53970,-0x7223212e04583974fdcdc21de72da6595b14221ef21f37b3972b6e8e8b14122ee949ff97c,0xa9935c96a79f1652cd0fb5494ae35bba806745a86c08594c776dee7b8d7f28d22c807d70,-0xce03bbe01f55ced8e1dd9ad155d216265d5fbea2138254f9f3e418c9eb729492ce5624e,0xc8f7db4729b823e62159f0110de6ecbb27757b1f0b3b4ba0cf0d942cba2ea5f161e3e0,-0x9a00c4323b8ac7691c3e05937f77c2eb0d8398908233bdd1e2646563c5c901bd3d65c,0x5a43a19722122a123eebbc0d2a580faf7426aea85d8e08dd75b0d62481dcb56e6340,-0x27283e6886677e74f43b94362be04b5e6e38c3f5f3bcea81764455b81e778bd1a17,0xc10ee5864c6f6bcc657949de2f192bf55f46d421be13993fd2239312503b1a668,-0x2819f6b16984606729bca2130739c0d11ac32166ce3d21d0d9d69f66ac03d2a0,0x53e63e17d3e25e7a9d95bb31aa2e8185d8489b87dfb769abe376ae43f005f8,-0x64bfb12d2c7a6b5d6fbaa2900674cae00779d5c204355ddf0ca072d0df50,0x3cea2a6e2cafbb98ea33b2c50f7bf506e9440655e5e41cb66943fedec8,-0xf2ea0270ccfff0a4006df3277ddec3723e7a9ddbd9cae46bd260b90,0x11a46ace23be745d11dedb2e90a6348b6fea859539675d34f73d8,-0x2bcfc35277db1920740086b062cf5c44874940a6df69e1e89]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 25 96 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 96 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 58 indices rho q29 m29 29 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 58 indices rho q29 m29 29 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [0x5a4316cc8201e674deee491296593d3c30e,-0x1f55bfceadab8e82fc7ff3baf39fb73ac6,0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r30 : List ℤ := raw_ints% [-0x3be68b4cd7f67920aeebae38e42ce5474c21eb3b77832f95d791b16e000000,-0x50d20a2d0bd4326c4a19604a557d860d50a78324e97cecce3f83c5b2100000,-0x33e949afff0bcd6edf7f9814fad06983fd5b0a1b28f763e51f32b56d810000,-0x15204bd924b94d8a09b93bc943f7b62f712da905ad7e7df963252efe4b6000,-0x61dd395f7ae49065110c7674eaa1356356f6302737795cc6c351b1e1b8800,-0x157472bd600a544a3adcb383639115fa6acccd9b72f8736764444b149b200,-0x3b3813802dab5812e6330aa04943cd766223f4da39205147f9da85107880,-0x83f1dc81ef215523d9957dab8d7c1f7b3c0fb1d320ff8dc99d3d0c91f80,-0xf1897201b06faa485f3c9bc1241f705204c0dcacde377215d1ede34f20,-0x16fcf2667c4ed6cced70fa99b3e16d41c207a2f3a7b05e5f833c0e18a0,-0x1d5f509858c3197fe79c1a092e5a7bd57e80fedbf3094630c21c9f818,-0x1faba69902a32a853999f95e645c89b502e0e51e4aab69fa085fc8f8,-0x1ce9ad956d1e20c7d5f63ed7748b43b362a5e84f743989823a78cce,-0x165fcdd6aabd9bc4192e3d9237bd4dd2aa1b80879f7f642b2b4e04,-0xea9d7c574bd9a928f6f4ce2ac132f6b6fa6c5bf6ba55f63e02dc,-0x81d273221a9857d585963ee1ce17e4b9d21fdd1e1714be3c17b,-0x3c5259e05af08712ca862b55a5ddd932f5005c77f87503dd92,-0x1756f6cb65aa1bc78224c3b371e3895261c58d0159c2dab5c,-0x76ddf47bc3c7962ce2b09adc1fdf65aa5896c10efc6da60,-0x1e971776c6ce8c55069560ed76a76bfee863e31073e07a,-0x634be6d95df52765a47dc5326aad8b84322dd6c1c4d2,-0xf494ae92f9dc3bf3fb070c3c9debeb238689d77cc8,-0x1ad9c8960d8d8eb6424982e7069937b3d697ee3ac,-0x1df6b24484c7d4107fa9224275bd5a3052eb4cb,-0xff7277009b928546f4f510276d716c47a82e]
def m30 : List ℤ := raw_ints% [0x0,-0x897e2e66933056fc6957d80de23586ab82d47d55cd1df83ea21a385e28101a6fa2f1d49000,0xf8c7f6a82518d3d064c5c5c522fdc16ae2336a0b5c787c7cf89eebabc377e73db5def785c00,-0xda044c3ca7575107e1301f559b1b5eae6b40464e58d08d7538c5bd36a60c433b15756c145c00,0x7b439801278d460597a9c3e91005bf839868a9bb672e8cf3d7e1d97d28db74e93320ead29ec00,-0x3288cd3730b180646e9fe95d2a566f32cb368246a9ec0805b46ccb5d9875372cc945cfac262600,0x1001ed05f98ad9050cde142a3ed9ae7fbf44b5b9e31545ef4b428c1feba202bf05b85ea1afa3ec0,-0x413a0112507a3125e3f1bff76585d03ba0e5e8035f01ef9157c0ee2895164eb0d9f3233c8da2400,0xdb88d21fa339703e915784484668818ba475279ea46608a9a9997bd739ba6f39e8afba9a17a5320,-0x26e467fc0454f905730e77247dd18843ea129fc328389064ef4f17deae0ca85111798b5337aa1600,0x5e317bd6d1089b3ab7b6e5c2e072549fe6f6aa32657694380fa9e44b1d0f34d32c8a1a9648187750,-0xc5154fe9d1a3e7068a86b14d8895ac038826fdf013e129c8a3af70b883549ae768934f8369a6ef80,0x16750f78c1959df981dd5e0bfd6eef2ad37a10248ef86afeecd7d620bbd6fd8b1fe5579ef9986aea8,-0x23eacda25ae0906ef762b5070bb8268413b45a708f85d3b05011314941986cd62381f1dd8a1405840,0x32a8dd01c57bdc2bcc707f1b2c7bfc23235f7820d57a5d2ea8ef54e891036755acec85f2121adb250,-0x3f464a12e9817d1a43e547afd5666fb1dfbd7e73ebfce979a855d3d89f2598e580c98d53c8dc1ee40,0x4635239900978e14437b60078d1b1dfd4dc9b63023e3238793023aecf9da133d1edb184a57dfb18c4,-0x455e0695a73ee4dcd7fa7e09421d9877711f29fc410608525246c42c0d693b4ca6ebca3c8a628ed20,0x3d219c801eaa4b6709d4b947f420ee7331e14866892ddd236414e95b548cbc4be1d14da6bf7198594,-0x3019fbb575a652ea528177eb93dc1b2ca8926b616899c6061cacebb45dce0766875fb993c59318c40,0x21cf2bcc90ad910d85a732576d3b608029c2e7c70022c77b50f5e12c0057dc775dd893b2b4b62f726,-0x1539aaaa9abda9b8038bb311b306ff4ed57f0d905deecc08afbbd2b6cddc10cf26f39a73b9a0e42d0,0xbe4f015de79f51d30797ed39f33ead757e415cd0bbca9e7a6b54d8aa0652079184c8a8d7231b9b54,-0x5f15b84516b0b2d9d633d85b0369027a1408f362477c594a995cbc65c063081e3261d4aa56a9cd50,0x2a4943d795adb444b46849ff6af3ec888b84f094e71712a635f60c1a395c0d7b609f6b22df5cb7d9,-0x10b37d8130db6c6efdb4f39a6c2a2c2c0e53fa6e969a4969e3222c30c0a54f2d0633e9fab30d1688,0x5d76b76e18344eabe0dca267505e35c45ef1e346ad8e98b52662fe91e682e53783bf9bc7c011050,-0x1cd98e7b21b7070025eee6734a88a772327f3ab5fe6509377a6301fc035a6febde7d6312ee884d8,0x7d3870a10a2eff4356e885717313b2c9820da3bb1372c6e0a6c30d7edb17fc1cacce3e5ca06684,-0x1db4d159e79c0e3c9fdfdb8c4e856b603eda95c8fca07aadc6cccbe3e895ec9e29895d28e6d0c8,0x62083d0ce52f3f4f9dc94b4f3c5ab81f21ab9496647ba83ffd1b4be921d6405962d78a09ac3c0,-0x11757de350a5fd639d7ef3afcb06cddc72f5a7d1e7e464a520e40e01cdeb173aa49edd2ab7658,0x2a9d0ff31062dbb78d492355b9941b0d55f5c17685026fd0e05f7a5e526d479387e33ed99353,-0x5841765bb2ca2071bef3c452654e1175e7ef06c20a9525197eb3b8ed3e269c6605f05203770,0x99635aee616b01ec1400cf2f3921e8ea85bfee943a9cdb7d890cc84b4a90a9291be5504f54,-0xdcceea32528a5b1783102653cb19efa91ee17f43dd639f478f0808df28a2e25e70cfa27b0,0x10339d96f511c66074630bd1cb2b0df16071fe794937221139dac99a2db3f9c60671b0966,-0xf3a2aae0d5405c6c79ca140a9a2fa955c482217be54b4d77b97e07e80aa896ae1507ae0,0xb346c835daa9dfc7ea659fa8b3a7c59b33456c5a0422541107669eb676ec8c1b8beb94,-0x6485cdc5a411148a7ba4351c439ddc2ad2fa650049433b570292f643d8869ef269680,0x298ad85c1c4cb57056f185a0cedf8a378a9f2f388bc80b56c36e861536d4ef72522f,-0xc233f4745af8b80e8d7fb2790115e8f15dec66893a22e5a8d410882f7abfae6768,0x260c367899a746c3dd13ca8fb7ce6aa78f69fd1449a705f4ea6302a3362b61778,-0x4aa3d09926a5c35871eff00c8209deab5a66816c86eeea7233f3e8137451338,0x537d7e818eada82b6a0b368fdad840c8e64e2cee38cb5f1815ccb1a918b28,-0x2ead116bb64cfb9acba24a97324524133757a5706889192a05ead10aac8,0xaaad02c4aa869c949fad4a929c04a350929cd759c9c588e9e6289c48,-0xb41c73de2f7e1636fbbbc9011399eb8ec65eeb61fe74966137c18,0x1915ee24d6cbe4e3ab7e61748a6599a650edd0fe2dcb3cc1e1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 25 98 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 98 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 58 indices rho q30 m30 30 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 58 indices rho q30 m30 30 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_30
def q31 : List ℤ := raw_ints% [-0xff7277009b928546f4f510276d716c47a82e,0x5a4316cc8201e674deee491296593d3c30e,-0x1f55bfceadab8e82fc7ff3baf39fb73ac6,0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r31 : List ℤ := raw_ints% [0xa985b0dcf701917d0fb7258004dbd37086f33146ea2d8c0e041ff908e000000,0xe4a944afebfbe0cbd72bd165a07647202ffecd49bc8ba88b0180f6739100000,0x92d335d3d809688221e0418f64610e6e74c9f1c32fdec6255b6e8d5fdb10000,0x3bbbc2a02a1a8209d6d5f46c94d5f3b28787d28b1e377837e17e3ad81c96000,0x1149c84d9c37d06fe682ce69af067b073533dce1c2d920583893dbb84008800,0x3c9e94867b9b9f7ef82ccc5b7f992756e8bca98ee9b3ca0dd58c2e0c71f200,0xa74106b88b119fecb01b2e1c3141a5d160804160fc30aab5a8af6a5e69880,0x1747fc26334d94514401a213e1016c8edb9fdd58f1e684cfd8886cf3d5980,0x2a996b00fa28f60f06df15ed6e6224784f0cbc2ff1a5d80071e328ed4120,0x40d6b5e50ed91811791018207590f91ec905ac051fefafa113746c556e0,0x52cdb85dacb355bbdea5c74684956ebb9f452a4de52453cef5f562c2d8,0x593be3f0a58d573900f027bc3c769f61c9179ea2e0beca31b6b8fe348,0x516aaa68b32c63fe0b234357aab348a56247c161ef3e7ea60fd203de,0x3ef723a21ee0b45653404840c953c7d4d95621f0a8ad481edb07510,0x293d0657737b80da10db4fbbc0acc0de4254d630dc643fd5f9e610,0x16cd7a5468e7424a3c6ace4aed1d5a806b1a06349512bb9f64280,0xa964fb2a1a11ae515594a20d9165e7f569590bcf50fa72710ef,0x417d158c5a5dd61a35ce26c103c01d0f5102636bbf5fb47900,0x14d3c05fe0a6da94790e3a302a5bba2059cf88d3ccf616f14,0x55ad178a4f5fa59809187c237c57d07e6e0037f61198e48,0x115d2b802d699d6a6430f0582ef51be80999d003b24410,0x2ab9010877799c75e6afb009346bb6d7d5d27a73a750,0x4af43426b2601ee69bdfca4118ade2369a4eb91bfc,0x538925110dab5ffaaf87032cea54776860a6d430,0x2c7299c3f28e3a4a89c86df97f9bf809c5318b]
def m31 : List ℤ := raw_ints% [0x0,0x11b943fb38f93b36899452d9ca28e65c1bdd64280f70dd0012e56144232a136864012c669000,-0x1fe51621e4e5963b2b45171d58fb7fa142dca0ab76eb880c1c0c7c61243274cef471bde83dc00,0x1bcb002f0ec28ea4992aa1107c0f0ae9b4681f95c0b48bb4d444afe90305ce1f7f2dbd133f0400,-0xf9f2c644d634242ff25aad6491a487631b75e913c53221e622b89d01eda802d4c13bf1382b6200,0x65d9078c764366f0a4bdeb25f8289d61839eb138b25b277fa0e915dd02e11800a67c0c8d4fe1600,-0x200ed4e93717fc17e6c8dff84fe63de2b2445108d842e3890733397451446e595d1c82d66168d640,0x81c5018efd189be55ee49ad089f58d3f98d66767fac7be941f23c7eb51c0196f6e1d9f9070751000,-0x1b1c80a37d342089cdd41d4368806d609b857a34fe5fbd30ff713c1057b395ff6d1999c0196eb1fa0,0x4c4ce7e5ecbe953e1366ce7cfecbadd2a161869357488a456e0e7e475ce38bbd8820f21edae556e00,-0xb76bb426960e194a35229f395fd84a4a93b706fd1e0788fe1a5d0e41a0b3968e3c5c7144a51118a30,0x17ccde7acce414fe62774e27b2b005f7f15c56b8b8f93041031a287abbce19f42c4dc7887bee6b5480,-0x2b0a841bcbc42aa76db0f51221cdbaadee567327570613eca76b7df6f0ce9baee77ee51c1e8ff42948,0x44419ffe611b713f02cc735e73f314150b94eaa273a539d02ac182da513427a566191ba1f0d567e640,-0x5f6be549027e1886fe2508793937c284fd53f06e5244fbb9b5bd34dee9b379a42cdd64f8b81d3527b0,0x7614532cfad4ebf5856f1436ed3941f8bbe1dea16545a30f0421e03fa8459453001cb150a9a0de8540,-0x81bef509035891bc00ddcb9c2a666733c46525c7b98ecfc0e17a40e21a8ddfad091a9e36aa4f159564,0x7ee334c40590fcfd6c27104f03bd4a37ef5d9b92c4e6e0b417b1e888ec969095604f174cad49474520,-0x6ea02d3871e5f634d3280b49d87056126df50af16d8cbf7683f60a3ef2213cff50fb180068876b7dcc,0x5611177d46c7934b5aaf19b6f03532d4b12339b39b4e51379f811793d69c5068367115249382a16180,-0x3bc6e9353e91ab773bd550c764ef8959d4df94914e7e36ea03379d9a6b42100f287b9c64464918f74e,0x250efe7d7f1253ff5e37804b64beaff7c72d555992fa20f3e3e353e9de2e7f3a46ff52ff2b1ca4e050,-0x147e2eec3605249aa70682664e0d224c8a472e77d80e9d57538c95b580bc1a0896c9ca45c3eaec50cc,0xa18970b1b01835b52cd6b5c601f2129a48a32f8741213543c9308932dd4058e74d6b1347008ee0610,-0x46c6dec0dfbdc18f0360a4c99d661bae2dd324cd90ae1897257e53d20520493547694f78a98f5fae1,0x1b83ee1b9eaee001ca41e335b157144868cf4b93938191061d0f6de8c2ad097d0970e1237e11f2488,-0x976af32e01a34c41b8f54828974ddf82195b33a96e1b977100c54cba07eba84fc45721227a3ff4a8,0x2de9017b30e7ee44b3f8493def44bf25778803b03430831c190a9afbec72fc8c8bd49f8662e9e918,-0xc380ee3bcf6e34ce4b3afba606c6cda7153f3502eed5493604e5196a2c84ca0f40012bef42fa3cc,0x2d718f183545ccc95b84cc3790fbe3956d231288ede22f7cb5f2c418c72c4732e68050f7a8e0c48,-0x92ba0e4f9f051594604ebd4f0f136441c315a373c35f5340c2bcd9f644a878ab2fa39794aa71d8,0x1986a9cdcd0827d320cf09d4c794f2c52f6738b321dcdd62df558666158ea6478af5950677f618,-0x3cc0de58d960eea17080e0bc46b5867f97c7af6b9fab5eaa4d28f13adb3ebc55cba551d2b5d7b,0x7a744dd051c300970677cefac54d8f72be2cbf41c732bbf1cc593eac86d5aac355dd86490770,-0xceaca85c8709a553c96cb6387054edaffe29c1b3ce7314c7457bafcefc0c7aa5692b19243fc,0x120381b35ac5b7b30be654a2466cc5ab464a51b061a7d3e33211d0a573beb3f2664c6b3c370,-0x146e88896bdc939206412553a1adbd21642eb8ed50ffe7d37a3bec03de2af89eb2e32cf85e,0x127f33aa99b75fb9da469c22f2aaa24b4062e95d264bd2cd919003d184373ab123d224f60,-0xd10f10fadc4a5bd7fb72e9434c3bebc517d8b9b1d76e9bf82d4e50437e203af7800ef7c,0x701bddb40846f061abeb2aab9e4d0e03a9d37f7f8a0d64b308b757df49ff4512e47cc0,-0x2c1f9139a74ec7032f062caa32e5cbcbc598575cf8a750fe86ace0dfe78b71dd76647,0xc384e6f3e2d1f1c59e6785958adaa83909703f492b6a460f91c1dff8ad909261968,-0x241e7ac9a6c90ddd4e7a16757a5d14f93695c97256526d25c02e7622d4625eb960,0x426be0fecfc1b9160e01fa5ff785b0fab53bb1116f5ef72b64aedd5ad82ba0f8,-0x45315c9f31d7e118f08f1983e4777e0a75d11b0d84f6aa76aab85af3a06420,0x23c32e556a58502a5ce6383e0cfd9375cb185ba7adcef09bf09c1af33f48,-0x77e6010e350f1edfa9e5e1a5c19416e7f1d40ccd90bd67fd66e2821f0,0x72e6711c4daa3907bd440bc8e89f33d400c0107e0f2d32658cea58,-0xe5c7f501bdfce1199eb3932f5850068fda33a88ac88dc16179]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 31
theorem quotient_ok_31 : quotientCheck 25 100 31 num den q31 r31=true := by decide +kernel
theorem quotient_source_31 (size : ℕ) : (coefficientsPoly q31).map (Int.castRingHom ℚ)=polyPart (key size) (X^31) :=
  quotient_from_check (key size) 100 31 num den q31 r31 (num_source size) (den_source size) quotient_ok_31
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_31 : cachedMomentCheck cache 58 indices rho q31 m31 31 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_31 (size : ℕ) : intPolyRF (coefficientsPoly m31)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^31) :=
  moment_from_cached_check cache (key size) 58 indices rho q31 m31 31 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_31 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<24 at hj;omega) moment_ok_31
def q32 : List ℤ := raw_ints% [0x2c7299c3f28e3a4a89c86df97f9bf809c5318b,-0xff7277009b928546f4f510276d716c47a82e,0x5a4316cc8201e674deee491296593d3c30e,-0x1f55bfceadab8e82fc7ff3baf39fb73ac6,0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r32 : List ℤ := raw_ints% [-0x1d7f2c95f0877207d5971a069606b8ae1312df31b9032b28ebc28f895fb000000,-0x27c6b151c4e2a5d2978f53f688b8e9e1a4713fbf5889b4ba259a7622974e80000,-0x19887efb0ef99653f2c5a415f8713b848657bc0da23c64c68522bdf8fd2a68000,-0xa62740c7e39fa5eb32b472116491967e4a31ddc78e0390ebfa005e039e507000,-0x3012a504439dbc777edfa68c8b7b8bbe93819c837e3270256620b00617048400,-0xa8810de67165ddbc1a80c1d0fa110ee21f39b93989cbb2f52a3d6b1bfd73100,-0x1d0be9181295e722b76a29f55334e672a4245b250182a4c2c7854e856edba40,-0x40aa5374346f86e43318da95c4f486dffc09e8f7073c3183795f34ad86dc80,-0x7645ee6181a0239ce9f5f554369189bdd0e305684be2b0138735e5a43ec90,-0xb3f03aecc5117deebb2613d6d1309de6b21bd4313f13e3d6d0aeb224d5e0,-0xe5af31c641a62ee0bae823386a355c04f35899f5267a20e4a9466b1092c,-0xf7652c8694420f6d3707548e5ea65b6032709452f564df3b8194b43d18,-0xe19988abdd97d57e2ba50a4a675dfa3d9493302409a11c153e7cb9907,-0xae5f14be6369c2a9946bea54144d5dc850285c999521cf0f32e2aba5,-0x7221ae0c8f4d2c5c7925df5b3d76f746172e36b609bd6d9e735d7b2,-0x3f11208578b61a71245e457577cdf6f11e8ce42974befe414a4586,-0x1d42c7d9fd0ff66ea4305bbdff76d2d2c9a3c2996bf98c77b5051,-0xb4dc3baa607431154a037ba9ef9eae4210e77bd2c624d901166,-0x3978b6278a69c3546f9f778594173968db60a4d303fc9de5d8,-0xec363c2e31ad523e3523ab012ef51ebca6f755a2514ed5b0,-0x2fd3e9542ae81e34a929e14c32a596f3f5a32cd49826459,-0x758e95a674113a717ca67254005cc6ddf3bb01c80b76d,-0xce04e033f4d59927a54d3277de29d919b7170a85aea,-0xe555a205f25face13fc283a33dc2c02f62396bfda,-0x79de045cac24d902d09065bc05e6443a8bfc5df]
def m32 : List ℤ := raw_ints% [0x0,-0x248e1c3625820a207bc1eae130f45b1df9789e929fd8c7d026f9189c8886c8074e426b9389000,0x416f1c5258544bb4a5cdb0ea66784aa1914f0b61a545c898f9d9c0885aa810ead82a97aeff5c00,-0x38b4688e14b395b300dfb3d73d867a6770b113c7d183987eda34dcb235fe88736b0af09ea655c00,0x1fb0a9a069a0836d205b39212dacbb576ecbe008983b4d7f25ce88222f353ba5163bb7a810526c00,-0xcd60fed3468d7d178282e65b028dd786c30b0608154dc164b9f6300e81a0d9f3307a847819e57600,0x403f04f9164c50932f5634311b97c8ab2cefa8cae8aa39d6d7ca619a942513ceb2f28fb683e2bdac0,-0x10264ca5cb7ca3bc9c463f68dbf2d9da29420f5e59a40676b8821dcc64cffe9169399421e1f8bbf400,0x359f294007813931f37099a5ee408dd545563fc97261d4af8ee28b247ab0c70fe8a629b88dcb474620,-0x95db0f867efbf200b9a1ec2c2c3e85d63b7d0074cf07cf763a2c0b40c0c0d707cbcd67c92c441a9e00,0x1659e2f4e552b893301df666b5cd6e90d01551b18ba2f10d8c6ce8ebda6ed82cd505c830bd22b991d50,-0x2e0cfc4e7a6fbb48f5fafe329e737867e3d3e1a283f88ead6074deb31a7645564a91d9b3113f605d780,0x529e0ab9d53eb228d09f3c87060a3164f264c3626524ae51045fa2448c4cf573a8797c18fcfefe96268,-0x81edae9ce19d3c6d99cb6eeefac368ea1a1e035a98f0d26401e2839ee3b74dd064ae9750359fc6f5a40,0xb40e73d6819dba145b71e7263c550dd2107665e65f3c70e9e65fe394d522ca7721f73ee29ad8d7e38d0,-0xdcc6f61a250512fabcc3bd5c86d8a37d730b1b46a9ecc383d3b5f5c60fd92f38dd3ecdf1f839afe2040,0xf0445456b5777b68bbb0d0c42f6ac715dbf7fcc66d34b1fef73b5c741434f3c3cf4b6ce40bed6959404,-0xe89c00cdcb49ec6186a7e795a9603491a641f273f3ff365e7e57c1469463aadeba3b0c0f8f1304c5920,0xc8a6fd03535527a9f2f47b6ff911591545c486517b98f23811c8cd73efcb06362b3d9c0fd39946f3994,-0x9a5e37b65fd1fa3b83b01908e86f3038a2c3a9b15c96a3ce8c928783e68b5c16babb70c1fbdbd295040,0x69f4a3cb27ae5ddb60c1028ee0b395bfa7bc8ff8c2ee56ca52317c25fdf52524e2195d37e41339e2b96,-0x40df4d80d3123048c3f85181e95d0c3a7cdc8b12278eb366d1b1b8165d57b8f890041d589ee160b4950,0x23673a6440b8a2e5c645958fe8da19ba09f25e8b4c6a3b56d7ffab6784b0f6fd094b067512a72fd5a74,-0x113321ffab217b19abe48daae498ee930cd9961f60165cfbe48699b0e952acd2a467730e0512eaacfd0,0x76cd526d066ac1ee694bd2bbce3283551a37a7709fabb5635e170e6243fb20288ef88d844e5e99b169,-0x2d76d3acffde585b6a3a27338543a26993e458c80a96044c758af325b87122a8439a642e2c24e04988,0xf608923ba714fb9a56ea0d32273a3aeceb84e926b21c63d691064320d17d3dfb93f03a099e8b49e90,-0x4947017741a5ae2f80e9a0d1487b35dc2bda5eff420007f5bc9cfa674dbf604d24e65861adf573bd8,0x132262ed21d8681fba992e498b7299226e1ca5b8a3c2786ce9f653a533c23c80d6033bc5dce1a0474,-0x45b9a79eb5038bea6e918a10abaddfdb3ccdea24955953663a71b43d0e29e168174e0b019fb8e848,0xdc41a2de9f78ef89c8f396f83f6e8bdd6773463b793381787d0288467a6e7b2acfd18dcedb3fea0,-0x256daa23ff78f8017be82e20cbf716c1335e6913157ea17cdd652a7556f5d9df8515eec7eaaadd8,0x56db9a8008ef40d98eadc32e6f1c5bf8f32eb7dcd59e70941ff7139131d7b94297f183d6fcdce3,-0xaa5c7e00f571b5f2056ac57ccfddd35d529b646c140c31a667127202bdf93e9eee266df5d0570,0x1172e23d6d61299ed44afe23d098e9e3a27732859aad8fd84ec58969161b8eb47c894aad1c6d4,-0x17919b29758af7736f831b93012f10552558055f692874c68f3f65d9a0789a662da6e89615b0,0x19d270e7bca76ccf8c07a28fbabd8b95c48127cf84fb55b698beca8669e6de49b9727a0e436,-0x168308dc2ef96edf151af1ba6ae391520d0d22297bdaa4a632ab0298f1eea5804473a36060,0xf431a24c794a3307e548a3afa89149748351f193365e1c93ee3e4fe96f5f7222ef444474,-0x7d33eed9e23d620edc2e31d082f9b592959391a71320beb0f25e20ad51bc0d2b174f800,0x2eea594d7c25ece407f05727161742f6eee80f074294f4c81b0e14d0db9dcce319175f,-0xc4ffe72fc00ca509840d8be954faa83b02e6e106e98c5cfc63eaa77beb40e993c268,0x224e3aab7509fdeb3142c932b22b5888fcfb770c4027a91dd322fbe1351818dc3b8,-0x3b1f788e6666251c51f3580c95a989e837084786581aa531d01506a071e9ad238,0x3958bc401855f2568b7e5ac19072c1f458a92d78d0cab93a6bdd27eef85c238,-0x1b65dc783b5febc5cae69d2c71175b915d8aecc413834d3517cb8fd130548,0x54366e51e18a4f1b711fa413987e17e10ec7df002090caa8f0991f1ae8,-0x4948fb3b3e29d2a8e7e8c5caa48ee49ba13432b20f4390d8e9ece98,0x8386ffd949b10226e9951fd238807b43f85aef710d250fe3351]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 32
theorem quotient_ok_32 : quotientCheck 25 102 32 num den q32 r32=true := by decide +kernel
theorem quotient_source_32 (size : ℕ) : (coefficientsPoly q32).map (Int.castRingHom ℚ)=polyPart (key size) (X^32) :=
  quotient_from_check (key size) 102 32 num den q32 r32 (num_source size) (den_source size) quotient_ok_32
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_32 : cachedMomentCheck cache 58 indices rho q32 m32 32 1989575339989487582360145270985767936000000 33=true := by decide +kernel
theorem moment_source_32 (size : ℕ) : intPolyRF (coefficientsPoly m32)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^32) :=
  moment_from_cached_check cache (key size) 58 indices rho q32 m32 32 1989575339989487582360145270985767936000000 33 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_32 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<25 at hj;omega) moment_ok_32
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30,m31,m32]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<33) : intPolyRF (mz e)=rfPoly (C (1989575339989487582360145270985767936000000:ℚ))*rfX^33*(1-rfX)^24*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U8C33
