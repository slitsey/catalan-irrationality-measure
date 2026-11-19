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
namespace CatalanCore.Li2.NVMod.FamilySource.V9C34
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,9,34,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6,7,8]
def indices : List ℕ := [9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
def num : List ℤ := raw_ints% [0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def den : List ℤ := raw_ints% [0xa9e39e257a09ca2d6db51000000,0xe8e8720f6375414ae8a15b80000,0x98347cd3235f404cce8c4f38000,0x3f1d3c1bc426510720e1a525000,0x12a61c83bcffbe93dce721e2c00,0x42e16209e7910298c75d7c4b00,0xbd1e08350fcca0d22c8780cc0,0x1b0a7096bf015d9752fbcff00,0x32f4b4d588862fc5b6df7430,0x501b9715f423bc20bdb2500,0x6a0548699e811e6c4649a4,0x76dcebd2d366e8e061dd0,0x7154f975500d1d1270cd,0x5c13b95af957352c8e9,0x3fc0131644f63ada86,0x258c1458f2b4d6982,0x12bdd379c8266093,0x7e15248ad9b79f,0x2c432fdc7c788,0xccfc60b9ecc,0x300ed4da03,0x8e539817,0x14039ee,0x20242,0x20d,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0xb,0x8f,-0x1b5f,0x1b5f,-0x478,0xa16f,-0xa16f,0xe3a587,-0x52c7d4,0x337ecea1,-0x4e0139,0x242f7713,-0x242f77130,0x388a2a0db,-0x28b1643f,0x28b1643f,-0x1091fc25,0x22d6c5f95,-0x5eccc55f,0x610e303fb7,-0x5defba8e0,0xfa7f46d]
def rhoDenominators : List ℤ := raw_ints% [0x449087b2f00,0x75045168,0x561cc0,0x812b2,0x1e480,0x2f508,0x2640,0x77,0x1c0,0x3f,0x1068,0x16b,0x4410,0x27,0x888,0x4ffb,0x5b00,0x3b8,0x440,0x286,0xa180,0x46a8,0x10b2b40,0x60038b,0xcb230]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-9) 0:ℚ)/(rhoDenominators.getD (m-9) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 9
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 9 34
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
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x18,0x114,-0x7e8,0x2982,-0xa608,0x20dc4,-0x547f8,0xb38ef,-0x13f370,0x1ded28,-0x261690,0x29431c,-0x261690,0x1ded28,-0x13f370,0xb38ef,-0x547f8,0x20dc4,-0xa608,0x2982,-0x7e8,0x114,-0x18,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 26 li0=padCoefficients 26 (liCoefficients 25 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 25 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x17,0xfd,-0x6eb,0x2297,-0x8371,0x18a53,-0x3bda5,0x77b4a,-0xc7826,0x117502,-0x14a18e,0x14a18e,-0x117502,0xc7826,-0x77b4a,0x3bda5,-0x18a53,0x8371,-0x2297,0x6eb,-0xfd,0x17,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 26 li1=padCoefficients 26 (liCoefficients 25 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 25 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x15,0xd1,-0x51d,0x168f,-0x4a4b,0xbc97,-0x176bb,0x246ea,-0x2b5f2,0x246ea,-0xe5a2,-0xe5a2,0x246ea,-0x2b5f2,0x246ea,-0x176bb,0xbc97,-0x4a4b,0x168f,-0x51d,0xd1,-0x15,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 26 li2=padCoefficients 26 (liCoefficients 25 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 25 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x11,0x7f,-0x1ff,0x36b,0x8d5,-0x529b,0x13a2b,-0x32a06,0x62926,-0x973fa,0xba93a,-0xba93a,0x973fa,-0x62926,0x32a06,-0x13a2b,0x529b,-0x8d5,-0x36b,0x1ff,-0x7f,0x11,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 26 li3=padCoefficients 26 (liCoefficients 25 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 25 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x9,-0x13,0x2db,-0x15f9,0x6361,-0x1370d,0x2cb65,-0x4d1f6,0x62926,-0x5695e,0x22dae,0x22dae,-0x5695e,0x62926,-0x4d1f6,0x2cb65,-0x1370d,0x6361,-0x15f9,0x2db,-0x13,-0x9,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 26 li4=padCoefficients 26 (liCoefficients 25 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 25 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x7,-0x101,0x8c9,-0x291d,0x73b5,-0xad73,-0x3135,0x3eeda,-0xb950a,0x154d26,-0x1c51d6,0x1c51d6,-0x154d26,0xb950a,-0x3eeda,0x3135,0xad73,-0x73b5,0x291d,-0x8c9,0x101,-0x7,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 26 li5=padCoefficients 26 (liCoefficients 25 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 25 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x27,-0x23b,0xad3,-0xa41,-0x8a47,0x34e03,-0xa6dbb,0x15b36a,-0x1f315a,0x1d63b2,-0xc3a42,-0xc3a42,0x1d63b2,-0x1f315a,0x15b36a,-0xa6dbb,0x34e03,-0x8a47,-0xa41,0xad3,-0x23b,0x27,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 26 li6=padCoefficients 26 (liCoefficients 25 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 25 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x67,-0x2c9,-0x88f,0xa77b,-0x36343,0x97b8d,-0xe7615,0x38f3a,0x26d856,-0x69c34a,0x9ef55a,-0x9ef55a,0x69c34a,-0x26d856,-0x38f3a,0xe7615,-0x97b8d,0x36343,-0xa77b,0x88f,0x2c9,-0x67,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 26 li7=padCoefficients 26 (liCoefficients 25 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 25 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xe7,0x1cd,-0x5db5,0x233f7,-0x509ff,-0x3071d,0x33f825,-0xa1d636,0x11b90c6,-0x129265e,0x81abce,0x81abce,-0x129265e,0x11b90c6,-0xa1d636,0x33f825,-0x3071d,-0x509ff,0x233f7,-0x5db5,0x1cd,0xe7,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 26 li8=padCoefficients 26 (liCoefficients 25 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 25 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1e7,0x1c0f,-0x13327,0x220d3,0xff425,-0x64fb93,0x104458b,-0x138c7e6,-0x42838a,0x3965206,-0x695b976,0x695b976,-0x3965206,0x42838a,0x138c7e6,-0x104458b,0x64fb93,-0xff425,-0x220d3,0x13327,-0x1c0f,-0x1e7,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 26 li9=padCoefficients 26 (liCoefficients 25 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 25 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3e7,0x83d5,-0x1df7d,-0x106d91,0x79dbc9,-0x119e67d,-0x116a7b,0x6382caa,-0xfed751a,0x13a25c12,-0x929d922,-0x929d922,0x13a25c12,-0xfed751a,0x6382caa,-0x116a7b,-0x119e67d,0x79dbc9,-0x106d91,-0x1df7d,0x83d5,0x3e7,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 26 li10=padCoefficients 26 (liCoefficients 25 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 25 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7e7,0x1ed27,0x5c381,-0x73b595,0x11ee1cd,0x274e44d,-0x11e8a455,0x24e8db7a,-0x16daecea,-0x2dcad4aa,0x772006ba,-0x772006ba,0x2dcad4aa,0x16daecea,-0x24e8db7a,0x11e8a455,-0x274e44d,-0x11ee1cd,0x73b595,-0x5c381,-0x1ed27,-0x7e7,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 26 li11=padCoefficients 26 (liCoefficients 25 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 25 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfe7,0x68d1d,0x47fc7b,-0x18185d9,-0x3d26aaf,0x22aa95a3,-0x40627f9b,-0x24a5b1f6,0x1455ac486,-0x20930407e,0x10b386eee,0x10b386eee,-0x20930407e,0x1455ac486,-0x24a5b1f6,-0x40627f9b,0x22aa95a3,-0x3d26aaf,-0x18185d9,0x47fc7b,0x68d1d,0xfe7,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 26 li12=padCoefficients 26 (liCoefficients 25 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 25 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fe7,0x1534ff,0x1c54769,0x256043,-0x34e794cb,0x752497ad,0xe20f204b,-0x4ae4e9aa6,0x5bce1f336,0x26820b1a6,-0xd91dda216,0xd91dda216,-0x26820b1a6,-0x5bce1f336,0x4ae4e9aa6,-0xe20f204b,-0x752497ad,0x34e794cb,-0x256043,-0x1c54769,-0x1534ff,-0x1fe7,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 26 li13=padCoefficients 26 (liCoefficients 25 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 25 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fe7,0x42bca5,0x92a6833,0x2f14251f,-0x10b6dd267,-0x1c49db7bd,0xd886df4c5,-0xd95545616,-0x1f196a805a,0x51713a61f2,-0x2fb35f8002,-0x2fb35f8002,0x51713a61f2,-0x1f196a805a,-0xd95545616,0xd886df4c5,-0x1c49db7bd,-0x10b6dd267,0x2f14251f,0x92a6833,0x42bca5,0x3fe7,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 26 li14=padCoefficients 26 (liCoefficients 25 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 25 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fe7,0xce7397,0x2b344a91,0x1d713905b,-0xbfec77a3,-0x20f9631b73,0x2b76f59f6b,0x97464bd9ba,-0x1790d228b2a,0x34532224f6,0x26c1bd9801a,-0x26c1bd9801a,-0x34532224f6,0x1790d228b2a,-0x97464bd9ba,-0x2b76f59f6b,0x20f9631b73,0xbfec77a3,-0x1d713905b,-0x2b344a91,-0xce7397,-0x7fe7,-0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 26 li15=padCoefficients 26 (liCoefficients 25 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 25 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffe7,0x277d86d,0xc106f1ab,0xd7fb2e157,0x2dcdaf5aa1,-0xc74293469d,-0x1bd13de395b,0x6774b1c044a,0x1312c803046,-0x12a7060e609e,0xd46d401a60e,0xd46d401a60e,-0x12a7060e609e,0x1312c803046,0x6774b1c044a,-0x1bd13de395b,-0xc74293469d,0x2dcdaf5aa1,0xd7fb2e157,0xc106f1ab,0x277d86d,0xffe7,0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 26 li16=padCoefficients 26 (liCoefficients 25 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 25 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffe7,0x78086ef,0x341e8e6f9,0x5695f920b3,0x277620edb45,0x6ad40ba6ed,-0x1b8079411af5,0x122d8f93c9a,0x748347bb63f6,-0x46c85f5feeba,-0xac98c4156eb6,0xac98c4156eb6,0x46c85f5feeba,-0x748347bb63f6,-0x122d8f93c9a,0x1b8079411af5,-0x6ad40ba6ed,-0x277620edb45,-0x5695f920b3,-0x341e8e6f9,-0x78086ef,-0x1ffe7,-0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 26 li17=padCoefficients 26 (liCoefficients 25 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 25 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffe7,0x16b39275,0xdc362c6e3,0x203195b5ccf,0x17931d2b0e69,0x495b3096e503,-0x8b25b0a035fb,-0x254741d2fded6,0x24ada3fb5d266,0x613ef5a916bd2,-0x5e22f0daed2e2,-0x5e22f0daed2e2,0x613ef5a916bd2,0x24ada3fb5d266,-0x254741d2fded6,-0x8b25b0a035fb,0x495b3096e503,0x17931d2b0e69,0x203195b5ccf,0xdc362c6e3,0x16b39275,0x3ffe7,0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 26 li18=padCoefficients 26 (liCoefficients 25 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 25 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw19 : List ℤ := raw_ints% [0x0,0x1,0x7ffe7,0x447eb507,0x39457866a1,0xb69cb5b874b,0xc11a75811ded,0x48283f3d372cd,0x551bfd96ddd2b,-0x18e3d5e7e48e06,-0x273e913dc8436a,0x3dff81621eb296,0x4c7c63b1e0b57a,-0x4c7c63b1e0b57a,-0x3dff81621eb296,0x273e913dc8436a,0x18e3d5e7e48e06,-0x551bfd96ddd2b,-0x48283f3d372cd,-0xc11a75811ded,-0xb69cb5b874b,-0x39457866a1,-0x447eb507,-0x7ffe7,-0x1]
def li19 : List ℚ := liRaw19.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_19 : padCoefficients 26 li19=padCoefficients 26 (liCoefficients 25 19) := by decide +kernel
theorem li_spec_19 : coefficientsPoly li19=liNumerator 25 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_19
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw20 : List ℤ := raw_ints% [0x0,0x1,0xfffe7,0xce441cbd,0xebc70945db,0x3eaf72b35587,0x5a99216e09af1,0x3390247a3df723,0xaf4b6a6a8af2e5,0x29b6a2b3cda48a,-0x2ecf868344dddfa,-0x28fa85b9bb824be,0x46a2564187e212e,0x46a2564187e212e,-0x28fa85b9bb824be,-0x2ecf868344dddfa,0x29b6a2b3cda48a,0xaf4b6a6a8af2e5,0x3390247a3df723,0x5a99216e09af1,0x3eaf72b35587,0xebc70945db,0xce441cbd,0xfffe7,0x1]
def li20 : List ℚ := liRaw20.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_20 : padCoefficients 26 li20=padCoefficients 26 (liCoefficients 25 20) := by decide +kernel
theorem li_spec_20 : coefficientsPoly li20=liNumerator 25 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_20
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw21 : List ℤ := raw_ints% [0x0,0x1,0x1fffe7,0x26c5c53df,0x3c3425be389,0x15087d39f4a23,0x282fa952e59a55,0x1fcb6805d42dc2d,0xb17346449f5d3cb,0x1832a22daf6abdda,-0x273a7b91ec5a54a,-0x4a8271c3e03f3b1a,-0x3963e6153e67af56,0x3963e6153e67af56,0x4a8271c3e03f3b1a,0x273a7b91ec5a54a,-0x1832a22daf6abdda,-0xb17346449f5d3cb,-0x1fcb6805d42dc2d,-0x282fa952e59a55,-0x15087d39f4a23,-0x3c3425be389,-0x26c5c53df,-0x1fffe7,-0x1]
def li21 : List ℚ := liRaw21.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_21 : padCoefficients 26 li21=padCoefficients 26 (liCoefficients 25 21) := by decide +kernel
theorem li_spec_21 : coefficientsPoly li21=liNumerator 25 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_21
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw22 : List ℤ := raw_ints% [0x0,0x1,0x3fffe7,0x74834f945,0xf49a193bc93,0x6f0f53539d97f,0x1125989af0d4239,0x11f6e09d62ebbbc3,0x8e7558c6414dd545,0x224c7870a5561926a,0x38f6d1caa1854fb26,0x370b6566a808c1b2,-0x68cc59c4e8848b1c2,-0x68cc59c4e8848b1c2,0x370b6566a808c1b2,0x38f6d1caa1854fb26,0x224c7870a5561926a,0x8e7558c6414dd545,0x11f6e09d62ebbbc3,0x1125989af0d4239,0x6f0f53539d97f,0xf49a193bc93,0x74834f945,0x3fffe7,0x1]
def li22 : List ℚ := liRaw22.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_22 : padCoefficients 26 li22=padCoefficients 26 (liCoefficients 25 22) := by decide +kernel
theorem li_spec_22 : coefficientsPoly li22=liNumerator 25 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_22
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw23 : List ℤ := raw_ints% [0x0,0x1,0x7fffe7,0x15dedee977,0x3ddc99bb47b1,0x2433b0e4faff3b,0x71d201327cf8a7d,0x9939e998da3d970d,0x650407adbd93f74eb,0x23110f1f632fd8c43a,0x68f7caaead7943ba56,0xa0bcacb80e1e9ec436,0x552608effcebb106da,-0x552608effcebb106da,-0xa0bcacb80e1e9ec436,-0x68f7caaead7943ba56,-0x23110f1f632fd8c43a,-0x650407adbd93f74eb,-0x9939e998da3d970d,-0x71d201327cf8a7d,-0x2433b0e4faff3b,-0x3ddc99bb47b1,-0x15dedee977,-0x7fffe7,-0x1]
def li23 : List ℚ := liRaw23.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_23 : padCoefficients 26 li23=padCoefficients 26 (liCoefficients 25 23) := by decide +kernel
theorem li_spec_23 : coefficientsPoly li23=liNumerator 25 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_23
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw24 : List ℤ := raw_ints% [0x0,0x1,0xffffe7,0x41a91cba0d,0xf9953731e90b,0xbb0f224c75c6b7,0x2e3dd9671eeef641,0x4e5fc9e010b055ee3,0x422e12e19f2d55a525,0x1e91be324b5492b4eca,0x833dabfedaf035cd9c6,0x15427b0c12746f273322,0x220a94e963152822404e,0x220a94e963152822404e,0x15427b0c12746f273322,0x833dabfedaf035cd9c6,0x1e91be324b5492b4eca,0x422e12e19f2d55a525,0x4e5fc9e010b055ee3,0x2e3dd9671eeef641,0xbb0f224c75c6b7,0xf9953731e90b,0x41a91cba0d,0xffffe7,0x1]
def li24 : List ℚ := liRaw24.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_24 : padCoefficients 26 li24=padCoefficients 26 (liCoefficients 25 24) := by decide +kernel
theorem li_spec_24 : coefficientsPoly li24=liNumerator 25 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_24
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x19,0x12c,-0x8fc,0x316a,-0xcf8a,0x2b3cc,-0x755bc,0x1080e7,-0x1f2c5f,0x31e098,-0x4403b8,0x4f59ac,-0x4f59ac,0x4403b8,-0x31e098,0x1f2c5f,-0x1080e7,0x755bc,-0x2b3cc,0xcf8a,-0x316a,0x8fc,-0x12c,0x19,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 25 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^25 := by
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
  | 24=>li24
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
theorem cache_li (j : ℕ) (hj : j<25) : coefficientsPoly (cache.li j)=liNumerator 25 j := by
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
  · exact li_spec_24
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x8365da521dce1f7adbdf0d2a71000,-0x133816fd21767a363eb37c8c306cc00,0x15eccf2f60a7c41272ebf058088fe000,-0x103f1c376e09f7a5cd84b0da84e1a3600,0x8caa1ffe34cbce49f0a83dd30718c8000,-0x3b40a1b18b471c1099f2a19968a17da240,0x14394fd38a3e782c44419f9b3470ea2da40,-0x5bfa82a9945257d989bc6711cf32a1e81a0,0x1635b49ba34909a3b1ef87262e78656d61a0,-0x49fca55add4ecc463d420c7c1721793cd3b0,0xd6fc6de4298a51d3da755234fb873a4e6db0,-0x225e244e267cb8722f4c0daf5ac8a50554648,0x4df21d96bc559080e89e417f10cb4ae848c88,-0x9daf067688861b0dcd30c88a517a15ab5e8f0,0x11de8c59290a22bfe7ee9332af9efc515c0f70,-0x1d278762dfd79ac87f90a7af5fa53089040884,0x2af01c067bc238ef9e2cfa7a34616d9a7641e4,-0x393b2eabe6f9915a2d6d157bfd30d095c6084c,0x452d20a1015d6977fe5853a6aca110cbda938c,-0x4bf13b6e8c62354b87c433d6418c9b5fc24c4e,0x4bcddd46bf367317879400f724fbadb4c8313e,-0x44d9109c1648a2306a86e5c6d20b5580189d5c,0x38e9f32dce353a00294e118ac295990676177c,-0x2ad22d49133b91e44857068116c854d247abe9,0x1d4fa19eefc7bfb05495425a3d954712182e41,-0x123d4204b53e54900670cb007d789b02e7f970,0xa4e52b30a8abe452120519e375d99adce01e0,-0x54794528889430a14c280f4255ec23f3eaa94,0x272848e55bb7f85c770e8778c5fe92de94b64,-0x10625cf3418659ae94da5870ed4b394c943c0,0x62b7d4db6e969ddd27f3b5b03623bd90e5f0,-0x2156b0d3061b6c50341cf40f40242fb40c9b,0xa0dfefc99bde52f4efb1b470979679cf953,-0x2b1cc5866a86441740573aad2452c70f74c,0xa34904eb6c5518fd3b463cb69fb636a8ec,-0x21e68115131fe03ba38af0c49e30ad69ee,0x61eef447dddf53b657ea26f7340679e3e,-0xf3887b4d68e0d3b57305de1760207e5c,0x202d4f1878428636d1c4fdb31b23f1dc,-0x38f14c920e733dc4895593b5d8ba30f,0x52bcef4ed53fa134773274cfdfb157,-0x60499dbf740b1aa900e21472dfdc8,0x56dd820e1b19bdff74d4bad98978,-0x3a1b591dc93e8e425fc837db848,0x1b0e48949bf6750d1fd82b55f8,-0x7f892a16a7c0ffb3706866d8,0x1452fff20208da78aadf988,-0x14e2924bbc97d448b9ce9,0x44024b24a6441c0e31]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 25 46 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 46 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 59 indices rho q0 m0 0 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 59 indices rho q0 m0 0 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x10f0212495d7920ed657c0b27891000,0x273b6f87f9f30f452f731620be804c00,-0x2c49bdaf28a974b9abb278123c8fe7800,0x2077efbcb40eed3b88f880b8f8478c4800,-0x11612702e42f510935f0a08eb8caa755200,0x73d7424407ea672d7df865025636c54b2c0,-0x27181297855364713794f3e6f218a30e44c0,0xafc35ab7258e209a380d2e4b0c4342a8f220,-0x29f1ed6006486a38f87b06400d641aaab2020,0x8a10754f7332516c732a744fafa39143f5bd0,-0x18c4b5d697a2170825e055705a115cd24c3a50,0x3e90690976845d85e119d5bac6a8cb2966a1e8,-0x8c178b9311b01c66d73d30c4113d35ab8f87a8,0x117b90d954ca3d90533a13e9ee2e61caf009810,-0x1f47236cdd311e5d17021f685f2a9015f726910,0x32561bd5442d72cf597656657ec5f0575af52a4,-0x4919b744f23d8b6731b33fd0b54d15b03194d84,0x600a9037f3990443dd3e2fcd0abde7399a1ca54,-0x72623ddcd49b58cb5889eef122f31d491fa02b4,0x7bae0ced56e25b7a37145dbb11cfd830ac35c36,-0x798b24279296af11d8c71d8128ad92a31b25706,0x6ca1bb423e385f8a8a69c9082d5628953d07084,-0x58542c5ceab970ac45ec0d7d4526f22c8b3e6c4,0x4155607f66da98d868aed2012ba59aa9663d1d1,-0x2bf0ce3a84b62459041748b4f353c731eed3d09,0x1ad990aa3180e607c7a0c1317cf229d12c73e18,-0xee368381708cc6c5f3c7872098264df1392f28,0x77acd9348fe76b9fdde55273bda4b81f5ff0dc,-0x365cc4f2e74dcbf40cf6f5efd020ccea40000c,0x1645ae4267534c36eac0ecf2abf793b5e64388,-0x8348053da4222351abc606afbff41f1430f58,0x2b54e1c1f2d19619c0f974fc0b902baa65263,-0xcc248817dd1c7ba861be0cf5eb54bdf6be7b,0x35596252f69807374089299f529e57ab65e4,-0xc4c82135c4f9a37b4fe9a66ed9cfc7f4ee4,0x27baee3f3bc1832fd9db35bc2f10b114ba6,-0x6f6e90528fee808eb7a7011568a10b0996,0x10c86cc8bdb14b933b500cfffabebe28d4,-0x224ed488ba1a71034b4d7ed498614aab4,0x3a9052970c4000f7c3ff1fd71349f347,-0x51d7a82cf89bcc99e89c65f44f71a2f,0x5b4a8229512113781ce26f9c0cde60,-0x4e9c8591313ea63a6b50f0f718870,0x31f04a1a0016b030f76e373bf4c0,-0x15f11c46ce7f21cc09587809d10,0x60ced476bffa4ce4d0ffecbd0,-0xe498419819e7ec22976dde0,0xd6872f96b46cdb2464461,-0x272bddf0ff5eae2ad49]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 25 47 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 47 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 59 indices rho q1 m1 1 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 59 indices rho q1 m1 1 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x22ef445b750c9d3e9a14fd7018ab1000,-0x501a16443d62b5e94e1f2822be289cc00,0x597f92a133497e345cdab9030e3ba5e000,-0x40edbf689910ae5f16d2613cfa637b31600,0x2262a2d659ac164a33d66d7dab5d06deb800,-0xe2b59d33e6c5aece8a453709e56f4897e640,0x4baa628cdf70425b1e142e35f257d20fe6840,-0x1505b1e15af1b2e11253d30409bb8239789aa0,0x4f5907cb634f6fc317627abf8822620bd160a0,-0x1021d70e152b9d090a0fdc078ff1a1cc73465b0,0x2dc02ab5ee182b3600a5a60aad039b368389e30,-0x722671c1a0eeeab8bd6fd4bad315f0c2be8fd88,0xfc67519f2d12172481e2d8c9c0a317086a06b48,-0x1f1861f69623cf1ec4d16ba6832edc88f9caa070,0x36e714284764d8d3a7ab9b2551d49d9591706d70,-0x572b8268c4b10ccf28f769bd42da485f1e973a44,0x7cd961281f12f26e3075ba52784f46a08db8df24,-0xa1b6b5f0630e2f468c1274bc34b884948861684c,0xbdce6db4d88ff53df1a6feaa2622adc65de9372c,-0xca2cbb1c5e4d2c0ddd66ee2c4db1b569bdb3dc9e,0xc3a36da0e6c435b4a04d6f0fc0eeed285a812d6e,-0xac18f97c0e79ba7a0b6c36768b5ff3da095893bc,0x89a8a32bdebad077b0e33e79fb2322366b2436fc,-0x641d290bbc627cc01587954c4937932e646b4299,0x422aaaa1d846f8401bb84b9c120a004a74a84051,-0x27b5075844d5d4d16dc22533b2f34f4a00164e30,0x159c0957544596cac50909a8071f5b692ebc90c0,-0xaa5cc9b4280603237179a8896e54f9ba6182d64,0x4bd78eb7064a8ab1805522b21d898486ce59f94,-0x1e6d4f1f766073bee2500d26a58524f39f01760,0xaf7763e95b182868efebadffc07ca0998c5130,-0x389b27dc4eb711686d12c1f978d4fc7712d54b,0x1045e8ea1e2a6e0f3770327701ea46bcce1ee3,-0x425a5da3b0ca17d5418e0daa60ae5db990dcc,0xee59a7ab3d0a3492964870cedfed55fa284c,-0x2ecb8e38a8f3fc56485e679194f999641f5e,0x7f69468126c3819de9ef55b91b8239b2d4e,-0x1297d8e2cda5844a199395ce74d431d77fc,0x24bf19e464d00af9079afa9ed3a0c5e6dc,-0x3c7d7305a43d2bde2cd266e9c57e2ac9f,0x51475a4ebba0a04ab8f969ae7bdb9907,-0x56dd38983da3fdf9b4c3471e6b2e488,0x475cd815e57f6a18626eb64bb24318,-0x2b06f500642f08823c0fdbc42c078,0x11d3db4d6a38e5b00ddd13592fc8,-0x4990c1f6d365ce0e64fb2663b8,0xa0c109c95d79a341167af1c8,-0x89b367679dc839120f8139,0x168e2dc0e4ca470d82a1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 25 48 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 48 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 59 indices rho q2 m2 2 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 59 indices rho q2 m2 2 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x480d7cfca16a04511dcb4ab732e0d1000,0xa394ce645256640669a3d7c612b3c34c00,-0xb4ef752ba16cf7064ce8128f25517967800,0x81ebe571349db1a2d59cc27c14c0c5c00800,-0x4416635c7636dc01cbadf76a0349b587d5200,0x1bc25258ff0b7c19ab94678c0b33d709d3eec0,-0x92a12ce791b990bf2a0ecf81737b0af0faecc0,0x2849acc056ba01e8412e4c3c03dbe4ec17d3920,-0x96592ffc3d1dee06e80a219d5466318cfa3d320,0x1e37029608fb14ecf7ff23cc13a0df0d27c2c9d0,-0x54adea45181183a79d190c5591530dd96928b350,0xd0bbe3459698980b25056b24851b6cef2f0edaa8,-0x1c7dab6451be9b6613ab492f5bdcee0eb44e1e368,0x37737c3ab7584e3aaa780feca9fe598316c62e890,-0x60a4080ea8746e73b078e761bf6cb047e73f7ea90,0x9767da72f7c23d15a7f693d82e22e19a737cafee4,-0xd5e7713af87dcab98a2ca26564fba0216554726c4,0x111330eef68ba3cb94d9201130f7e7fccb5b5c8254,-0x13c1069065c246c4d1dabffef350d94e476a297374,0x14bb304daa913c57aa1031651a12edd7cd7afaede6,-0x13c1bb0f1f6b09d72e2d45908b0ee95a67e1930b76,0x111ba4c0c55c3b539021cd496f32ae39bf38ab1c24,-0xd76cb4280eedd76d728b6940db14ae184bf330da4,0x9a109af219f6b8ebac0f3c71da841a6d4e4b612a1,-0x6412db1bdd5490dc69750b0d4d142dc160fac9419,0x3afca795f2dd21e93fe2ece9ea6dbd1b390ee5f58,-0x1f82a8a76d3611047980bd8f78d0cfdc334c9fd28,0xf3aaa07d14d4684cb4b6d201f03b829bead27f0c,-0x6a51acafb2e44aaf2ee8e3fbc186810a803d76fc,0x29c566176f9bc09c6671f91583c4ca59c00db7e8,-0xebaf010a82863b243579d86818d77faad86f0f8,0x4a50dfc1dcab516548825f238de961248f53633,-0x14dbe39bc1d47c940cb04119a3241be65b7388b,0x52f0379f587d678b974dad477173f3d56ea364,-0x122211b6274840cf563f6c924a0a28ac5e00a4,0x3762ac6eaff867cb4c2e3c4aef67b42b20e36,-0x9260a45a7fffe3ead10cff7f0e3b88386a66,0x14b1a36968cceb99936a10ffff1ab5c71134,-0x27885332b6b7e74288544bc0afb0f3422d4,0x3ebd77cc900722d820bb61e6c682a29a37,-0x510787debc5a27debf8584ffd23e20ddf,0x52efe43751b8e18ebebee20b259515a0,-0x40f9876c9d4aa281245631ced7e1af0,0x2529443b989ace337e35dc40862190,-0xe828d35a2c1c2a31b8323aa75d20,0x37f5d764acaee1465cabae07af0,-0x71152b64038faa877cd1c37c0,0x585ed4db2a7d17b69297d91,-0xcfbf2097585f7d26b439]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 25 49 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 49 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 59 indices rho q3 m3 3 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 59 indices rho q3 m3 3 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x949bd1c90ceaa8e74d734a19d8efaf1000,-0x14e20ea9e1147c7f7aae917055b92c2ccc00,0x16df0b907e9497c1391c8f990f83169c3e000,-0x104217effd603bdd80c92e108d4dd656089600,0x86eeb08d31edca9bd956461c999eea3aede800,-0x367023c3ae4a337cd16d9e5c9f23b36a6624240,0x11c7ea8e6deee573cbd2120b5de12fc0e33cac40,-0x4d518a1cc0ba6753cd7c51b65ad5a7f0b5e131a0,0x11d57487ba7e270fe4a29a9a06fb0dd9f244567a0,-0x38b195b30bae42a554b82fd85b77bc76c4923d7b0,0x9d0bdfee0011526db887489bca028d6e8e7622a30,-0x17e870cea07a8a9dd08626c82ac5e08f3e4ca16248,0x33943091c545599272371b2813a49a57919bb30008,-0x63237647198bf9126a9a198403f6406d3478d41bf0,0xaa93ec6a4265837c1eba9d1e3d40aa61a05ad5e2f0,-0x107bfbe4c1687538e1879591c676103984258879b84,0x16f9f68145e835f213aa3aad262f1806f6ddd2fb064,-0x1cf0f5503a90e51f496940426e23835b55e65b83c4c,0x2101ff963fa421508c1a46fd72f5452bf93177ef1ac,-0x2222c25432c97e7d19138991a368e21f2eaab224e4e,0x200b01627de921a546e84e6a9221aafa16595abff1e,-0x1b51541bbc1cb344a5a4905b44e0daf982c8f4df51c,0x1527e5b5fe8edb0cdcafe92d9a5aed8b61877e1c4dc,-0xee163ed78f73f70ed934b8ecd13c40f7e2aa6f41a9,0x98031fab714c1d7c2feb6e8a94957b8b0b2675c761,-0x5804a946145f4618b6ae608ae1c224a3566b1503f0,0x2e28390f238f5549e8ce30ea6ad999879db816e300,-0x15e229d8217b12c1de3c9368a099a7f93f5f9acd14,0x95bfeef92b75be43cf324b582adbf72a988bceb44,-0x399ecf56227a0bcb27875f5ea2371ca25bbc43100,0x13e1ad4e1a0eb3a7f96ea04b5531eed3239468550,-0x620b310a0cce9ac085a97ba96fd3dd1b296805db,0x1ade410adc12ef9868b542c10aaa81e0d1aa1b73,-0x682d0d6ca0112de286e193c5fae98ad4b2f2a4c,0x162de2a4a646b8c2aa9f930bfda393602e4484c,-0x41dd887c07740191e33a10bdf3a78c6e7c3aee,0xa8f34bfd38a1aa1861df1a632eedfc8e470de,-0x1722be9d16c846d6b8d80f1f077ab428e009c,0x2ab670816606bb1981dacbf735dc45d85cfc,-0x41563715eb7a8e41f3399a91cfc3f053b4f,0x5114bd5f00ba7f86277bad59a1e2d1d7b7,-0x4f7343e5834d697e225cc53c58ca60048,0x3b5394d0a3a097e3860b0c0d060ade58,-0x202afb14845d53495eb358d67425ec8,0xbd437b5110e5de1d613d1db237a18,-0x2a9ba36cfc6a8fccddb185cd5498,0x4f91c4c78e63ed6da78e58ac28,-0x38b378e9027f0cdbfdfe1aa9,0x778f1b211995aa0c17811]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 25 50 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 50 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 59 indices rho q4 m4 4 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 59 indices rho q4 m4 4 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x1328160aeaaa3fc5d0fbdc8d54f6e5911000,0x2aa9fe5c4528f3fc3b28f1374b6deb1c64c00,-0x2e4695d7d6a241fc7543df5690c3cd2eae7800,0x2092787e11d2ea9da3fa7deba57e40967de8800,-0x10b9e4df70b940f053643690ee3ebca1df49e200,0x6add8dad79d4b744e8813c00cc0c123fdc299ac0,-0x228a654ddfd08cd0e214868271cddb11ec20cc8c0,0x94981c2d75e9253489cdea24aa02a19a4598e0c20,-0x21e6736792dd600b4030cc8a1456ab7e7c7f9a2e20,0x6a914c161d486c21477f7d5e6c75c7ea05b05997d0,-0x123d5d07ce464cd279e31a81ba5053bf323a0eb0d50,0x2be8b45cecb88efdb6ee30434b352de5ebd66b27268,-0x5d98b1aa6e988f65fe4c9fbfabc204d0bc5e7421928,0xb1b2048b046f29fb8542d611d8156d5ae3f14099910,-0x12de6ab9f078cffd928e6176c4db4da10c6904524f10,0x1ccc85462444241339a29ddb44dfdae35d57332d3a24,-0x279bfb99ac0409f562f01390bfb460a84b9b36cb7804,0x313685427b0f05725294b4562d241dc2295e81af6254,-0x37578ae7e1790a5082ab77a2975ca927bb9aebf1ae74,0x38687250c551d5932f73e9948ee2a1eb14efbcec7f56,-0x3429bb7a366918b71244222f46378d945e1515820866,0x2bc9ff7230dbb9214cb9814bf938357285a0eaeacbc4,-0x216008efa72c52b32e1c121d0baff03ad3536f8cd644,0x17174b67d48a26de46386146d082b6ae2d0edbbf2831,-0xe7e47059f57501d11780938375530c6337d9ce72529,0x83e9ca5194ab7d36727660a328a492a7160474b0298,-0x43ea565ef844f28ca87fccf30d7f072b85dc9e5ef68,0x1f96ddd0868440f442e2fa1d36719a95da117634dfc,-0xd3e78612e7f455860883c0e4df7b30b176fe77df6c,0x4fdbd87b4e3a1365089ce8a3eb93b489e9c3b27e48,-0x1af65e39acb31b60ba4a5b69e613ad0f9be0676458,0x81f7d6d676bc0351b526f499bfe2538883295e3c3,-0x22c66088074f8215a0289f01baa8169b574679f9b,0x837a68273968ad1cbd1fa9a9e439067c54a23ce4,-0x1b41bea463e0d51b85ddb4504ec35acf5c0e9b24,0x4eb17bef4c921337fb72360ce1cfe97aff0f806,-0xc3e3e9f55a5bf1bb23c04fc243c194f581deb6,0x19faa5e505a68335379929fa4fe74c2fd1b194,-0x2e5765b9a5e625e3a8a43b6fa3b08bf77de34,0x444ea6618fb051b2d4faa18dcbfffaa93b67,-0x516c7392a96ce867d7036c5cf5a3cc3b18f,0x4c5a45e7c3302d7ab7241ed7e39d6506e0,-0x3650e838e18d2858d297a87b46c8d1530,0x1be7c9db6ba75deebf7344fbac87f7a0,-0x9a87242c89843ef04f7a10a19d95b0,0x2078111c70a47f606e6eb09ea2c10,-0x3800199f898cabe07271555e3e0,0x245f9ec03f36a0377883ed301,-0x44c9f2227dcdef7e239429]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 25 51 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 51 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 59 indices rho q5 m5 5 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 59 indices rho q5 m5 5 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x2782ad7683ff2387ff0776e37f3d397b31000,-0x572e1cda1881dda2d6463c0140d2b4ea8fcc00,0x5daaf3fbd4975158192409af844555605e1e000,-0x414b94f2014300d471372eb7ff8db13fee409600,0x213347a0202473b20f99556af36502467c1b37800,-0xd1fe18ffa891e70ee5e57a4f5696b5d085363de40,0x432d618d5e7585482ba0172b8847b1dccf36242840,-0x11df865b964014a7379e7670a6276f1e16ba8d998a0,0x408ad5d5339af05c09cc200462ffba021be032bc6a0,-0xc8ab7e4560a09ba7941dc52f32c648d9f0712a999b0,0x21f5ed3bbc9ba212fe2c3c15bf46621fc395054bd430,-0x50d0b87cbc26f354fdade2b71ac3fc1f9f0ed98b2308,0xaa3cdedeff3d62f72c497523bf5736cdae513b0c8ac8,-0x13f4c7558563a7bf2ac0e5a97f697dd70c9d346722370,0x217c2ca38322c3067dcf9048d589a3e4f3ab07f2d3a70,-0x3274fba90b29919592c72d48883268d9cb782ce14cac4,0x447d64e78a090339c44d853eadea8baa5568fc44061a4,-0x53f38f1b37f9e44e47afac1e77606069c4151bdc2804c,0x5d1989ef1406b8af61955b15e6261e0197a954cd047ac,-0x5d8a2398cd0e8a09b40d556c99f6c4c8e55dfac0e30fe,0x553a588d34e03f43f4486f3c03d09b89b7c1cff19d84e,-0x4675a0100195fd6b81082cf9a4889360dc7e8ed024d7c,0x34dc2c83758ab0d3fe20b296a03043e397d446862013c,-0x23fa640db9de57195cf60be0ffb8c5dd4d26b15c42239,0x1633c124373d5e148223ef7d01e51899df9bde3487271,-0xc68d3f69f0463a47f2f18a891fd23dc5019c197efdb0,0x645f20cc279cdc104dd9f1317d69070f32e44a5756c0,-0x2dce2e90235d1afc8b36693c24aac3575ca6ac52c2c4,0x12d3aeb64b05910efa4212b9dbd1c750b13fe48b8974,-0x6f3195d7d7ac366f1273ebd074e96f3953cc18591a0,0x24bc7f486683241ffcef6d082b8a37a52b89d9961f0,-0xad1946ab6e13f787b911f3a4ce50aea90385313eeb,0x2d386e10926cc8a2243690cbad0a548e57d67db103,-0xa6b6a37add9033bfb7ae590e5453b7c0f51fd46cc,0x21a6f18937bebf0d6bfc5d4e13d91c899b1ea4acc,-0x5e729912f831d3f9708aeee23dc62b33b84ec77e,0xe421edf36a5fd2f7546d8dc5330355b52b1a8ee,-0x1d4be43abc17818b78fc75804c7e39b53fbbe3c,0x327b7fee22845fc61e12ae355f81eeea9d269c,-0x47aef2b2efa85f8355ae6829a849d2131647f,0x520cf74cdc228505efb5bbdd57268aac0067,-0x4999aec472da8c27b3f347194631fb3b808,0x31db76c5caaf4de058b9f1001f77a63c18,-0x1841c7f24dbceec593f09d2a8ed18f918,0x7e58816edad83f781bb4216e853cfe8,-0x18c2fef8f8624bd75f73cd6d2b6678,0x276b68e2271653fed0dfa8e12208,-0x175416079ef9ff2143aaa58199,0x27916616b8acf271952de81]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 25 52 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 52 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 59 indices rho q6 m6 6 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 59 indices rho q6 m6 6 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1]
def r7 : List ℤ := raw_ints% [-0xa9e39e257a09ca2d6db51000000,-0xe8e8720f6375414ae8a15b80000,-0x98347cd3235f404cce8c4f38000,-0x3f1d3c1bc426510720e1a525000,-0x12a61c83bcffbe93dce721e2c00,-0x42e16209e7910298c75d7c4b00,-0xbd1e08350fcca0d22c8780cc0,-0x1b0a7096bf015d9752fbcff00,-0x32f4b4d588862fc5b6df7430,-0x501b9715f423bc1aaf4e500,-0x6a0548699e811c5d8e99a4,-0x76dcebd2d36698a7cb8d0,-0x7154f9755005d290c74d,-0x5c13b95af8e58c81dd9,-0x3fc013164007b55986,-0x258c1458ca378059a,-0x12bdd378cce8f3eb,-0x7e15244044164e,-0x2c432ecbdf848,-0xccfc30e1510,-0x300e6e8db3,-0x8e496071,-0x13f7cee,-0x1f8ee,-0x1c5]
def m7 : List ℤ := raw_ints% [0x0,-0x517d85c4703e39487dff6535366e468e151000,0xb22e1bf96646a5f5127470c100329523c894c00,-0xbdab96cb976f07575a914996f0fcd493ed467800,0x82f87c21bccf760b4c42a68fb7ac93d8e55c80800,-0x41f3d04b2cb686b736f7d9049aef01d87676fd3200,0x19d0b74e434a54b0ebb8885e3bb63649e20545e66c0,-0x82ce214d3c10885e46062d43f2a03ef0732e326d4c0,0x2271a92f72ca2d1aadacbd41e408562ba87d06738720,-0x7b12ad5f80a910ec631d0b29924129646c7db20a6120,0x17a86d850a866a23aaf13ba771fc0ae9ca8a471c375d0,-0x3f5a8ce399fd7306cbf79a155d83e5e29f3b9b2c6fb50,0x950e7b71c29099912c1aa17916dcd397c4f0135c49428,-0x13658f74474cc368276b0b2e964b3fbb6e98b221e274e8,0x23f29cdf971089d6b5409a135aee86c9b2496f7e0bd590,-0x3b94b025606a5bc1b995fcdb67001d2776aa7ef9a8cb90,0x58a6f850fec9449fddeaab0a5efff91f44a1c3d0f44164,-0x76c837ce1bc0d2e35891cdcb5f875356d5774595503944,0x8fa99aae816bdd08d8a7495f1dfd677360d7aca60b8254,-0x9d2316cb77eaea5dd5daa4a3a9ad551ab1060dc3627274,0x9ba6c5aa8577b8b19f080621b61d87a56e9274db0bcd46,-0x8bc1557847e0d273ae89be404f2dfde663831e0cbea0d6,0x71ccc33ae7c361b16386fd48f98453b3f96a741df54a64,-0x540be06bb8cc26a4a77b35162b5a8ba150ac6ad4cc04e4,0x38486430dc7d579c914c10ab793323ec7022fa303540c1,-0x2226f0a6046de1756c0190ab728caf2cb925becf23ae39,0x12c1f82117b228620e8a41ae56686c5fe189103cea4dd8,-0x94fb9ba8c707f900df063126f5e3e62457365c2d58aa8,0x42b69fbeeaf2d1fe4f237f91600b1de4d61fc25adb86c,-0x1ae236590b1b072642c42d6a5af0d99e534101859e25c,0x9b879d3191b94d3011e8fe10fb00d139f34e4194bfa8,-0x32489769d1d554fbf4143f9fe2ac0ddf4675ffff59b8,0xe79b84f869068f8a5194e87646488da2a47cd33ad53,-0x3b1337712331304545dd46f355e4308a8f8765c4fab,0xd45cac31cb23ae90597002b053ee398378c6b6ce64,-0x29bc85474bb7e27bedaccbe89de9c8227be0ba50a4,0x71dc3358ad2c708e1c438567dc3dd1d5ec8c97556,-0x10ad47d8eea1ae1a7b61ef69348302d70b265cb86,0x212cb82e0f82f62c92fa62958d367f84f4e266f4,-0x3735ca90acd17e92bca81b89c7decdb54a18b94,0x4b809e203ab1653a956967b22072d818c10397,-0x52f556287641a42fea8c88ddab975b71b933f,0x4727cfa1ca860051372797d0127c952fe820,-0x2de091ede0d067bae660d4f2c083cc78e70,0x15203d7a8d8983d008f67ee32d1d8f4830,-0x677069b90f2133078178d01daeec29c0,0x12e5a12ecb978f53d460a49afc3f230,-0x1bc07628cc0eda2efff6720c00e00,0xef56718fde0f130f63ef0b7e71,-0x16c113b3ae5711deb6e6bd19]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 25 54 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 54 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 59 indices rho q7 m7 7 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 59 indices rho q7 m7 7 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x1c5,0x1]
def r8 : List ℤ := raw_ints% [0x12c9fc6d850f352c26321655000000,0x19b796e37158472bf6037d1d980000,0x10c6bf86f8e3417869e95a6d298000,0x6f1686e04ef46e215060bceb41000,0x20c0d33901ac65ea9ec41d5118c00,0x752e70b34af39daf1af9fad28b00,0x14a780e65467c086a5c55ef244c0,0x2f1c5b328aed9dfbf3ab0f72e40,0x587a5cf46ea55caf6769ab99f0,0x8a91870c807ad8e9943e904d0,0xb6999fb186383f13ed6b6a34,0xcbb498c5762d084f344276c,0xc11d8eaf6970cae724e1f1,0x9bd99766a636f3eecbd00,0x6b0da630b8795d5c9145,0x3e74ded001798465984,0x1ed125f0f28870de85,0xcc5d9630e658f870,0x4671916d23ffd5a,0x13e77685d206b4,0x483a7b97b23f,0xcbcb7d9300,0x1a85d21b5,0x24e81dc,0x1a813]
def m8 : List ℤ := raw_ints% [0x0,0xa812e3e52780562583dec0bdc04371850b71000,-0x16c3d1aa18a674ff3e717528ae5685399cdb2cc00,0x18037e57e96bbbe9bfb04dc4efb2e22239cfffe000,-0x106db8a6025fbbaaf5e10ee0445bbfe7be5aaa29600,0x831dca75df49ddd403d89c097edd8b77237e6fd0800,-0x32d39f418cafb2293ea524b2f75a951e24a9a1365a40,0xfefeb0807f5c268950f250839614365459d9bc646440,-0x4277c5ca0b70bba0521fc76f8aa194ec01490e8f257a0,0xeb0b101037b17e346925f3020edb3418bba79b8b2dda0,-0x2cb403603d1291a5792eb86e8896df868c40cf4afd4bb0,0x76696ddc785fe4fda123d190d6df970e8b5a4c2569a630,-0x1137ec65fb4ceb8de39310b07978334c3f4ea75ba1aa9c8,0x2370d83fbefd9dcee78dcae86fcef1e47e38891e18bd388,-0x40e971c59d99614fc4bd06b5b107d385067358e4e3a8ef0,0x6a4a7143e3997b4fb987fe09074c9a3f9f025240caf8df0,-0x9c31c03ad0ac5f70423d2d57f2b269c2477b7208373f204,0xce9c92ed3a8e9be51e550eb7933acde7a9a11578b7ef2e4,-0xf69bb4242e95c118cc7edb02b6ecf8f30652d97547fd44c,0x10a167d848439aa6bcf27a017bcd2bf9d59cd4cbcd4efbac,-0x103e451249eb30c1017362894cf49a0d5c0988a797796f2e,0xe5fc18d96b39906cdafc963809a810891c79c1b8995dafe,-0xb87ade039380180a8bb0c3edfc7ff6ab18596b90567d2dc,0x8624fed838f658200b86b534b1648aafd7a4ef6c7cb589c,-0x5865319dcedcc9c6dc127cd0c5f97aa2df805a2e40004c9,0x34bf7be057e01a7a199bfe5f05c5475c7e7da0a7bd55181,-0x1c78d0b6a82e4d7b160ef12292bdb7328f7fa9bbcb0f370,0xde1527f2de16fe098d8a482e44d6f50b2afe2fd0867480,-0x61969b8b6bef27c71d4588df0ee2ec527009ca496586f4,0x268ee2bd394feecbf3fdef61ef61a5839bf6b13589dc24,-0xda84be8c18794d739426a853ec5d8390268a78b9a5740,0x452331bcc43dc6bfaa56068385435a9baef0cee4d4190,-0x1374c2440783e473766980f1bbefac06d00c2dfc986fb,0x4d861bef14811b911a1151ac64821e7b85525faabf93,-0x10fb9df5ad8104505baa4ab9996a926d2105484ee34c,0x33fe103735135c93a15dc6b718addf649f3291e274c,-0x89dbe4f5d7e04a144bc0cffa1bd938e3d8af9ba48e,0x1396838f11590eb43d0147d79abe17584d445edb7e,-0x25b7dc4560188896bc472d974007a3bbcda19c2dc,0x3c9c877a52d64fe623b92862c6ddfa98516c713c,-0x4fcea32e84b2b4ccdcc7ddf16d5273471e8a1af,0x54254f5e73f9d8f95a18032005adaeef12d317,-0x44fc493e5a29534f25a152007ba8ee35113c8,0x2a5057438b727aa603b932c7b09f8cfaafd8,-0x126eab7e8a413bb950bc747b1fcfe0582e8,0x54c9ebde42ddcbe1488b5592321103f38,-0xe6e27708f27f2a36a84bc62f5613b58,0x138a1c1c8be12c6f62484b987e1ce8,-0x996ecb99b336884d67d383b4389,0xd14fe7fe86abaf5e73fda5f1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 25 56 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 56 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 59 indices rho q8 m8 8 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 59 indices rho q8 m8 8 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x1a813,-0x1c5,0x1]
def r9 : List ℤ := raw_ints% [-0x1196d99d2cee845953f1306f03000000,-0x180a5a6631b8da285277762207a80000,-0xfa86c134bf2bde1e3c6b7fccc7a8000,-0x6780aec10360d0f44b5e949db727000,-0x1e756b076e7fa631e987d48a2693400,-0x6cbe33e71e2995b1919d5ff7600500,-0x131f4dfc7496bdcb117aa1bb346740,-0x2b80d431a243f414294fe326ca840,-0x51774df7ed4887354353fa0df150,-0x7f2bfe794c11f8723a26ce02510,-0xa6f785e28654f069fd2f46125c,-0xb97d1eff96649e65abe694c3c,-0xaf01dcec78e7d89abfedbfcb,-0x8c75a78a7821e4dc4c1ef5a,-0x5fdd4167e27b80815f6af2,-0x3781f0b5c90df10219361,-0x1b247c6b6571d2864965,-0xb20b3a26bc5dd71a48,-0x3c8cb6dead1f416a8,-0x10d1fa581f9eabca,-0x3bb4ab1d0f1f85,-0xa38a8882af76,-0x146ac38e9aa,-0x1ab865931,-0x1172d1b]
def m9 : List ℤ := raw_ints% [0x0,-0x15aa6f608a178b1ad5ffb6d875c8b1a2267991000,0x2e8ba08cb7c60483beeae6e3823272c6d3840c4c00,-0x30a9e44f9e7daeab513964d78f14df31352d35e7800,0x20fdbe3f5b1218273dc59da1b311ddce0938dbdd8800,-0x104dd97e01f5906b86d27234fa1a615f276054c4c0200,0x642a919b80118167be4dde391440f426d5ccbc29812c0,-0x1f1a9b2705db2e4fe045278704d85b34f0c1ca29fc00c0,0x806fb9d1b9e635f14aad7918263630d7b94e87fc47da20,-0x1c1904c4371b3437fe9b5df6192870832adedbeaf696c20,0x549cf8796ce20ffb65ad04cec50792a84a74b13f74f23d0,-0xddbc2be2bca954341d4db1f8112edd815890a3780e0c950,0x1fe3c4642c585ab86aa6407249f36d1465868763b3ea5be8,-0x40e68d65abc1413ebf86f24c2fca996f2bfe89431109b6a8,0x757eedae5d7d39b6206111fd82c705c36f42d33d40928e10,-0xbe1c024e3c79d4d86aa1b053113222953dc554f2c294b410,0x113f3721f417a0b81845cc602d071ad51339538f28d8488a4,-0x1686de1362020aa18ffdfd13fa03cc3057140a9770354aa84,0x1a89f119bba845ee241edb86b28422b4a1f46d79584030254,-0x1c407f76e99397d8ab1e31aa5302c41cb45973c325d879a74,0x1b367b0f0dfd759f79e803d870cb80bb14d942ff4132fb6b6,-0x17bcc6a541bb028187df143c1ebdffe6b795c04f726f514c6,0x12c267f482a3a203d65d3d5ae60ce44653168cc8db76e1404,-0xd6ea05db39ad83acc788dbaab3df337a0fe3e868ea0aca84,0x8b5f115ff7d45110eddac02218cbdd75b10cdc49ab2a5551,-0x51cbdb9fe4e9fc6c8485c1823ffbc89473be84649a58ff49,0x2b65176e970bfbf5b8dac4a3cc0f559c83a358166a880918,-0x14c714ef307c41bbeab34c9c6831cdf458c0751026fc51e8,0x8f5d3cfb8c92cd35bac88c1a198c1be4b1cd5391f354d5c,-0x378b0cdf9278e45ae227ae75a58011f4d2390b362108fcc,0x1345e89c474edb6eb49ac3fb9e5406c4f87dd685ccbe008,-0x5f7b7b32b8a6a718a7d81ed67569129a8df2fa0ca60218,0x1a4448575ee4781082bc61962839503e31cd290de123e3,-0x662f870c67aa190e04b04a219e3afb95b3b537bc798bb,0x15d37415c07ff8ee0411da6e5f11266547e50fe7467e4,-0x410cbddfd0199dbf00bfdc96687e992f3044b150aa24,0xa79fd3598cebfd27a18bd98c8597f0b5cc38ddfab26,-0x171a093387679fc0e4c1d14c9ed5f8ee2db417d90d6,0x2b0d7c1934c265edbfaa87eb265b154e09d781f554,-0x42c9bd445e02708daa585ace7a2458f0fb2b465f4,0x54a59e855bf69e921af5e483f6ec1a61038095c7,-0x559d481920bdf572d3e354194c682c5653962ef,0x430fd92fc359fd6937460ad369758eca3a0160,-0x271d3a681abf862f71ae6c7eff0feaf5353b0,0x101c054fa2572d74869ac8fd7e2eaa4fe440,-0x45945ce6608a6f83581f072044ac616950,0xb0688b0aa7f2efb7f20f46f79ae27950,-0xdc21dbbee358e41cabcbb49e00d520,0x6256ca8c5e63551ad74495ed2ee1,-0x784f87fb4f5bd6ee5bbb69f09]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 25 58 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 58 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 59 indices rho q9 m9 9 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 59 indices rho q9 m9 9 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x1172d1b,0x1a813,-0x1c5,0x1]
def r10 : List ℤ := raw_ints% [0xb9450048a64512ef14df67d5e8b000000,0xfce4f0218351fcfce6569297a9f680000,0xa47b5fab32b8bdea893bdb66a0b868000,0x43d9748cb43efedcef66079d5a243f000,0x13eed18f5a2175c5aa8bf446d6f783400,0x470813d4558bcf5b22cf8da2cfe1b500,0xc77129ecfe86c98ccf55d5e2cc71340,0x1c4b2f8467408a85d2d15186f8d7dc0,0x34d99e35364183cbc48388fee108d0,0x5244ba15e609a49c3120e1e8ff5b0,0x6babb01fd031990ad4359b37733c,0x77303e035cee3e28b4d5c4ca294,0x6fffc1d2b0c672883c7fc7a263,0x59799a6107b9fa0a6ed0d65c8,0x3cbe35d13a93b464b3e6aac8,0x22f473abcc23693a8048fc4,0x10f80fc68e46fb0b197320,0x6e5ac56b951836000760,0x252452015faf985d910,0xa2fe748792c8384dc,0x2396a74e746bd987,0x5f8183588ef5e8,0xb9ad05d442a4,0xea2450ed4c,0x9101272e]
def m10 : List ℤ := raw_ints% [0x0,0x2caf85b71cd08ee7595f691e72edee5e6f5abb1000,-0x5f2f7b5e04e5cfba560646b471c80cba1440595cc00,0x62a7873010134a959731bac228aa9f1e0faea81de000,-0x424a095e23484c5dd702e30a1ff96dbda8f23ce8c9600,0x207679979bb7f54ca21c18f5e6db0a5f8da49643a51800,-0xc596af6e6c9d74fcd33b4835840e82a38dd4748fe73640,0x3cc5db8c88e82f37c1eaeafd391525ae089d61fc9568040,-0xf88150733e7669fb6ae382059780e6049458b9ae4a44ea0,0x35d2941916a2159af0346b96669dc2bbfe0546d03d52eca0,-0xa06c2fae3f106037162c770c1a9f4ed55a8eb97df5d5edb0,0x19ffc7d4b5c0ce6a62a50c2af5d0b725bd9ef4d3e1a984830,-0x3b2e923cd1743f1ebe5a2f64a21b1e8ee83c6aec96eba4e88,0x771c59fa8966ca719f0cc050b0c3ee46e4a43497330dcaa48,-0xd52ebc2dd6982736f11d9608efe37574bc3ac2650cd9b9e70,0x154e412879fc87f888efdbb76b4a664e66773ae53bb6006570,-0x1e8d8fec02e765c33ec1b0ab8b66f863a391358c14f7399944,0x2769096eb283df0136dac3f219264edd822f6f332eb0ef8424,-0x2dd584918e0897718a436d2fc6d8dff8ab9ac67edb28aa384c,0x3025a29516633cb7746ec0fc992061c21c57e8a88939a6d7ac,-0x2dbdf472b0cf690327505019ae9760692db30d9c1229be4ede,0x2755fe74f4bc5f6bd811c0c88e5eadd5bda22eeed97c426b2e,-0x1ea1aaa2adca6fea20e458966ce0d25b725960f10e8a7cf53c,0x1599931893341009c9f24661083b2c9ebe8a0c25eeb3f164fc,-0xdc96cc889dfe6dbbc1a62c7c4f21b6475ac2f622ad0d32359,0x7f57d14ce4b6b798c6d782f0546ec95236f7147e36f62ac91,-0x42684fef338e09d5653b38a7b1b9a46b66de4a3a429bf6530,0x1f3b48a797e098d7c509ca7c8802eed31631d46928ac75e40,-0xd3802f0cce9a73de7f89f40cfb5aa6d23599f613acfbffa4,0x505a470bbc8f7fa6dcef7e52189e651ad9ac76280ce74f54,-0x1b50c4ea60d3d0afb311a2c68f1571fb29899abd2774d1e0,0x8470bc716daa04614b5dcca66aa707b3b0594aee9549630,-0x239dc1d3388c345776aa8a2cbeaa2c6674118530791880b,0x874768cbf3e4c3229f9eb24ade979a48bf5ba981390723,-0x1c2bd42120e817d18f67dccb8d2e41c97b3240bb12ffcc,0x51bb54747e4d9fa0ae6f540463ab3de960da7703e3bcc,-0xcca9311975363ec1f5bed63ca7aa60208e001199741e,0x1b5adb64b5a4d7f323eb11508a2915800ba8fb49c48e,-0x315460897de01f159494ba00b5f7431c7f4ce6b1e7c,0x49dbe0210a4d691c4eeacd2664a18306a5894a6adc,-0x5a13ffa45c33c0ded5048275d23527e726ade50df,0x575e42c2535cbe967c0fb15e9a71b4f8a14677c7,-0x415c2f8940d6cf052e8267bf76e6da94ba69388,0x243ba416d6821d39f5824fc6980b57aa29c798,-0xe1a10c72b207dc18be6cd1669f133840d638,0x3928749f4e992a8c5b207c9e7caaeab6c08,-0x86da34c2c319d6e3ab3a23cbaab824338,0x9b01a26f937d94f3571c00e1f7d3ac8,-0x3f036f8392406c80781be1812b679,0x45232d5c278bf51ec9898ebe61]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 25 60 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 60 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 59 indices rho q10 m10 10 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 59 indices rho q10 m10 10 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r11 : List ℤ := raw_ints% [-0x603ab0770c4325e0f0e03ba55bf8e000000,-0x8333702823e35f487bfd92f367864100000,-0x553985434acb5d21a24d321cecd5cd90000,-0x231b5c72166bc72c855858da7c38973e000,-0xa4c5232d60d8a698dc02649dafa3dbf800,-0x24a3088c630012bbe44fb9529a974a4600,-0x66ae5b785f74c8defd22de2d84c61d580,-0xe8997c958cf306a0e497cc223107bec0,-0x1b182235d03a8717c890e6f91b7cb2e0,-0x2a12630e4bf39798db5f4f3aa229d30,-0x36e92ca197cb4092d5ffe438ed41c8,-0x3c98ef9e5c2c81d3fd033c63c9824,-0x38bea01885438be8657239ffdd42,-0x2d279a0aa25121a204e979cf67b,-0x1e847aab5715ef2d410956484c,-0x11789f74786d59efdea971894,-0x86e53295a68dba5cb2a2fa6,-0x36727b4d1bf297d99dc472,-0x122c94ce89686a2d38b10,-0x4ef78d239838c8dc398,-0x1108b6b0bc77f51cae,-0x2d0755f279dbfb9b,-0x55e0bdb1bcb4dc,-0x699cad223338,-0x3f3b0c6c0a]
def m11 : List ℤ := raw_ints% [0x0,-0x5c2a03c9ab6e26bd2854c8cecd0abba2c5ab21d1000,0xc2b0eee97dd4c94589f086d2952c9a3fc9c4b84f4c00,-0xc8130d0bddb914fe91cded630a4c04929b3af60f67800,0x854514bbcbd424c6f040d1b4a782a888e5ad9077230800,-0x40af35d4362922a0945a855addd41b9c34886c5734d5200,0x18620be8126fb017c1a1737848e52fe804cfa8a647e89ec0,-0x76dfdd23cafc74d00588a21daeaf7a145cab320a74db0cc0,0x1e17195f9427949a23f957e8a6793ac6f8d75f70433a78520,-0x6740876127b3fe7c3849ce4e00339912a303c059c59190f20,0x130a840d2606980e63fb78d386f7d310f6268786882f9b21d0,-0x30dd745f4a235287436a1fe0006fec83ff9572f30acdfd2750,0x6e0d48bea232e83964eb207912b8053de4987cc3edb75a29a8,-0xdb13cfa81c8166ce5121fad820820b04a56c5b7e8451554e68,0x183b3c5917e0d2ea0c453806760dd1a3954b4f7d8fa84ab2290,-0x264cbe42f7e9d703ac6ebb95af4b423fbc289443567bc707890,0x3644f1a807064c8440772627f6908a58c578ae9c38e1eacffe4,-0x45249033e2904c91a2937f32c8e3d87ebe32e0b030581596bc4,0x4f64ec4cb9df00c7ce84bfa4237801f908b73fc445dbe5f6254,-0x524f311971195c64694f912f189930c202f766328d42fbe1274,0x4d23c53b8eddc5cbad14d38ca0747c26880e9914b52e5c6a3a6,-0x416842c3a26adc7b3cce077ba9dd77004b7207767f2e4077036,0x3231c683fe552e208ba024f93d46b0064f12e2e6239353420a4,-0x22dc9f75afe45f96c6d888d2d0a736f9ce09e792b050b515324,0x15e7544ff0e009824ed9fbbaf71d901b425701bcf5f3eec11e1,-0xc7060dc74c3548f302dc0f3f4025dfc11ec84c28600fd94059,0x660786a82d92666d2f88144399b1b99cafc8fc3fae159f5458,-0x2f22f8a672e976b6a722e0f12d9183f886e8d8235883745128,0x13950c13ad0ecb8f710b83d67cfd0ae95fafc8f7d518081ccc,-0x74bbaf968a82b53945b987b388fc0d6a61d5db5b85e7fdbbc,0x26e0eb32a1a5666225e642078e0e71fe92b830e4fbb325768,-0xb87d565c85f746ba56465082570c3bc10151911ebed2e978,0x30802382d7a99d7cb20daf0c0570a7eed69f1f33372bab73,-0xb3da8d38115d0d842149682ae71d4ad6da460d34d4f3acb,0x2483c0966eed6ff4f13061219bb2b1f02950cc80da50964,-0x671e3d8fb15beb5f48bd09aea3d173f0ec6b9bf85d0ba4,0xfae44cb117cfcb96794aaf3568fbf75ea0b05f07dc176,-0x208482f23a796c3352d30d813a0f25365c62032d922a6,0x38bb5fe6fd685bf2d75c4d67b21e41140a11edd9c4b4,-0x51f69a359a61b8a0c0635f851483ffadfdfedddd154,0x602a4167c299a59b893234f864061b8add895ea5f7,-0x5969d8e4dfbd7f9f5206422b1b2b006d5f71ee89f,0x3fdbcb6888582698e2e369a53552dcb3002332a0,-0x21a1a23ebcb59dac2bed330a45a9015f5f658f0,0xc5ce55e75e615fe5ffbebf48812e358a14bd0,-0x2effc6634a4517a292332083acf151077060,0x67217cdb804992c7fc17df5c7d9c968970,-0x6d261c4fede8af4177013479cc54ed40,0x285e3ee676d3e2b650c39ebaae3051,-0x27b8a732333fef05f28a102a9f9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 25 62 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 62 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 59 indices rho q11 m11 11 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 59 indices rho q11 m11 11 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r12 : List ℤ := raw_ints% [0x29f6339f09bee6b82ed7a5df3b6bd2a000000,0x3926b240cc7b6f8da8fc15879296eeb300000,0x2514d2c3442a500312a096dacd7a007730000,0xf4187126dfea4a9edb9d229c7d26241e2000,0x47812d833edc49d0120c4708fbffb649d800,0xfe01f2da52ed64579c1dda3f1a6f6a2f600,0x2c6bd295655f1e035f9c5161124bbc73980,0x64720117a1cdf8278bb96b988040942080,0xbad5fe29df6653443dc3524cdbaf70b20,0x1217c249f5fa3fb2751fd76688aaebf20,0x178e9afdc75dc99626a1518a775d7338,0x19ed35eda706580df502bb03da3a858,0x18347e7f46f1f40cf537e2acae4bde,0x13322d9f5b9aefbf8709151ea47d8,0xcec7f6e1f600480b85cfb281ac1,0x75dda72484d4b3c68b384aaec8,0x3897fbc3c8614026f7f8ab12a,0x16b5f5d270ba4202bb421090,0x78796b44d045480abd66de,0x2074cf1bd9b7c762eb8e8,0x6ef434f7594bce00486,0x121eafe8f5c98c8838,0x2210c8833c3eafb1,0x29241e786339b8,0x180f6b575d4a]
def m12 : List ℤ := raw_ints% [0x0,0xbe16a7cff1932fe6232ede2a86e622ffb7b0f5bf1000,-0x18e4aedb0bafc78c9dd87400f28abfe239025bc238cc00,0x195e86e41f62f8c3c1d3eb4e5e17a20714c40e66e3be000,-0x10c141088fe0cdcefd7b86e7b1488d2764efc0ce50769600,0x80fbbd5c41b16de353b484109e6446cb18327ac1da69a800,-0x302fe9c40e2fca5d14068af49faeda516c431159671bb7240,0xe8c7946f7f59fff47477fc21e0945b3201d285bb16a0dfc40,-0x3a5ec3d17535a89a95a96f0d5bb6f8264643f4345b6f1bbda0,0xc65d7c1ab035cbf64ca5c4853cc9008d6c002b0686252fb3a0,-0x2438450b4e38a49ab0465288bb53b8f221120da98e70fc1ffb0,0x5c01d741855e971be7b436d5276532cfe22432c6a9b16f4da30,-0xcd0d59c72f8d7b995cc2d4ee8075681adc8bf77a789fd47a148,0x193cf0d1854d219f9c277d8de499525b10a10d36e83b79beff08,-0x2c2b8d333d0cac1aab53c92106cb2ba9cd6e49613cbbe9a8b1f0,0x4504f9eaa886165a8836830e7ad8ec449ecd08e0d8d0101d40f0,-0x60a636fe5e0bd0c8d5ac05589c0886628e04e93cbeddc0b80084,0x79a535666dfb5ba812382b440968f2c83e0bf04bd594cf35b564,-0x89eeb0a072dd13368ae182cb3b9854ae653dad165ccf15812c4c,0x8d256b8b1efac740170f0dc866fccc5e2a581160f1ba15f483ac,-0x828273a60154dfa5c5f35cd98dad0f666c127239fc35a8f1240e,0x6d1fe9ce98b02b13cf28c02b91e6c59ffad4a8bfec9560aff4de,-0x5289f5dfcbcf39fd0fd8c3e52a3bfb35a5ff739d350403c06c9c,0x387848deb9a783901e0a0d819ce00d341b497efaf380e70dc65c,-0x22edd2578bc4022a627e36254a35b924c55cb714f50be53e6de9,0x1383f0910c948b9228b58bc85eb0e7a23691903be89920286ba1,-0x9d602c0a829eafd06cd51f1a461e894584f3f04f76d0c6df2f0,0x476d50e69af47a5fa6cd5fb9334518d9a4f2ed034b9f72cfc00,-0x1d209e869aff13e476bd3732455d3b319433bb5a3fd999b48d4,0xaa49970635b8b5358ba8b8c089d00d1fa14d500eef5cf53704,-0x37915e20ff346218ff0b1fc7c95769b23dc37948a2ff46f980,0x10213020943d70ae7530008f22852e27b6bea4e59592a85fd0,-0x4252ce45fbe49ac21d4afe2da69ada4214752f884c6ef6a1b,0xf01dc19b08f3dac9678b5d11ed18bdb0c7ebfd9536a547b3,-0x2f866278beb784fd3e76642164debf395f02cc61267f9c4c,0x82a0f5d20707cc9872cfc174be23db0879d96154e51804c,-0x134c7e68ad830c9d56d912b2511aa2438557a2822cd022e,0x26cd3f8e9f74245a05ca5784c979011f0cc548d9d5781e,-0x417b2203df5822dee8e87da191b13646da85f1c29f91c,0x5b43b973bad90f33be344c4077160586cb23aeecf37c,-0x66fb2b4e8f6a5d574bc7c33de4d8008445060c8920f,0x5bc2374e5f4217d326d0f7ab7d36e0f79ad4d27677,-0x3e89dd316a9750bff102ba21695c83d72800f9748,0x1f46a5f3574623587b9212682bb09b737d68db58,-0xada83d1c42f060847097eadd6ad63b060ba708,0x26ae0de6fd8621e70cfe55903c764102d1258,-0x4ee6cee57e3251b071ff6441bb883884618,0x4cdb556bd48cfd5053297e4c0ecbbfba8,-0x19dada2aa714b2434daae81647ba269,0x16d0ddb9e741d21e9c2ef3d417d1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 25 64 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 64 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 59 indices rho q12 m12 12 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 59 indices rho q12 m12 12 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r13 : List ℤ := raw_ints% [-0xff79265e5004684fff1eeadd834ed26a000000,-0x15b9dbc524bb09847fbbc2b01383098f5300000,-0xe14efe6bc5d413b08550de3b0bd6a6f8b30000,-0x5c975fd1eced13c8a9996caca1496cab682000,-0x1b170b2be2c8b5996c0fea390358a0c2969800,-0x601a7432ffcf85ee7ecc0f65bb82df3e2d600,-0x10c832e0b1d1b9f954b799c608a9b2df27980,-0x25e2faebccdd3b872d19f6fc85e2627d7c80,-0x46590a730fe1b6e82130655e4665588e560,-0x6cc93609e04f4c561463db6a88e1d2a6e0,-0x8d56568e95f1269ea5259c6fedd1f1e48,-0x9b2f5349fac0ccce8f4ca5bce0ebbae8,-0x907f783f461f680f8f12616e1566bea,-0x7241d3c1a0076034c63cf8666b6c7c,-0x4cab5ec488770ceecb201820590e4,-0x2b89ce502cc01fd0d6c6d9ba9ed3,-0x14d0f27671ca4571863d6d7a2b6,-0x85013cbc96d793a9f972225cc,-0x2bd979e828292b2edb3204c0,-0xbbc6b1a3cf80ffa8a29c1a,-0x27cfc07c4f76d7e9062f6,-0x67125861e9c125b4d20,-0xbfa08117b11f1ac94,-0xe4460fbd995f163,-0x83380a9c7170a]
def m13 : List ℤ := raw_ints% [0x0,-0x1880eba1ce23f92caa890aa37b63aa82f6adcfada11000,0x32ef68c1ad093ec753af54818ede2bc29594dd409524c00,-0x337ccf67c8cc834a666c25d47f15a7b7f56b2fc7160e7800,0x21b8bf5e3484743885ea3e54d680e5e19f71e7e97a1a88800,-0x1016297b3b8391fa1fa53face2f2cb9c9bb240dbbd0fa12200,0x5f51170974e63b05be8db1b1b38c87d29439aa2099410b0ac0,-0x1c852a77577ab915e3e9ea1677d734fec42b12d633b55d1f8c0,0x715f1eea949f46ff2d798b76d43e22ddea094b7cf8e3efe4820,-0x17da445056ffd3c26ea172c1ef9c286532803093f47338ec0a20,0x45020dd1cebd9343d7fe3632dde9fd87c9c2aee34d321278efd0,-0xad8c2a9e428d9ffc0e03ac13625ef787b7e40ee42325a35e5550,0x17ece21b5207f67a9129a0692b1828c57f342a68fbf8a952aed68,-0x2e9e30ad60bfa390a7fbbf450839302c2428ef1dfe3b8e272ec28,0x50b2fb875f93e8cbbeb9b5e667b2d3eae3535137828651efdb310,-0x7caec8aac9c9793bbe339e0115433fef365be3b4795ea9dae7910,0xac927d65c7a711964ec645306cf7af67f2d8c656f1e3ea0460724,-0xd69ab3576522398f692abb47c46e7fa0802a60a2b2b635f019d04,0xf053bcdd8778aa380ad96442f7010499be8eb6936a541aa8da254,-0xf2c7640643417299f3c06a422e01d321c59f6f664201068638a74,0xdd81f63aa287738857a8e663b06633e0743171e5b96caebe00016,-0xb6aab32e20477c0044e2d703221b23484457dafb347e16b79cf26,0x88318c2653e817864de9eff5e200fef21475626d21b0a8d199844,-0x5bcc1b386a135470cb852f28c57b911cb1fd88a6461f05c0216c4,0x37e7abf0d61f3fd85825ebf8eb4369d4af2fd9146a5996c134e71,-0x1ebbb56884111ced282f12d0865efb7c1d20c4581c8cd54333969,0xf3af433b49561eef3e257cb1df2b73454f40518467a1685a2f98,-0x6ca99962f866fe19696bb79104f337c7e949e0c52f18055a7868,0x2b7fdfb2c72267e79da8a4ec2b7305b2d0ce4506e2298a469abc,-0xf96c400ed02dbd49490251a681c64e61d5b221d63d1353cea2c,0x4fbf62b0f2a3e62bb87a5b6fc2aaa1ac56bfa785409fb22adc8,-0x16a7fb16359ea41c59703a7bf42515f7ba817ae1ae6aa9327d8,0x5b11f5c5c279a24c4f13a84a28d6b7328409b1194efce3d403,-0x141e2a4f169bab1c7fb79b16419aff23f8fcc45b51a9d035db,0x3e1b0efb69246748fdeebbc51bfe898d8ded37b52649972e4,-0xa622c62de79fe5c0dc65c455540a55b67341009792c94524,0x17d7e171a760f67e14a3e79fc4f3d3e8b35cb5c2d35c8c46,-0x2e78cf05c13d358fdbd5a513148c0092336b5101920e4f6,0x4bd84bfaad72842a5c55beb601ebd37cbb832763428d14,-0x65f44a1e5d393f34439edbfdf35b055f1139a7fda75b4,0x6e9c1c9e2c3e620b416ec9e30f767c8a722598a74c27,-0x5e6a1c2f80a7b7977abf336171a0b7834bf7a898c4f,0x3d622d7b6fc71426936f0024030e4d49925bc73be0,-0x1d234ca1fbd36565f72eca4f2ff79485e1a32ee30,0x98a815c144547c82a8fe0e0d3ccf01e01245ae0,-0x1fdbe7bba9badce363dc0ab0642103d9476af0,0x3c6291629b2b96ae8c4af331e662e2c29a90,-0x361dcc05b96a07092563a2311ae846be60,0x108e3adb88352ab7ab0cd48c934462c1,-0xd1a4237c6633b814d14b99534de9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 25 66 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 66 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 59 indices rho q13 m13 13 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 59 indices rho q13 m13 13 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r14 : List ℤ := raw_ints% [0x5714aac27bcfc0c6370bc3900c9f0fd82a000000,0x766275b7de41ea86765af037a0a7448df7300000,0x4ca88fee174c3b60fa11e918e49692f91cd30000,0x1f7877c6a5ce121e88ad14c03946af0fa3b42000,0x9327e53b73555f72ce4d157e5b34d64b3b99800,0x2096888b724c5a760ff9839e597c1b05c015600,0x5aee1d588120ba993a21efc9a8a0ed5332e980,0xccfbfd6a858600e1863dc9eebdb83e3587c80,0x17c0307ec987ac42ec59faa566eabd6fd5d60,0x24aa17041ff3ee659a14f13b430594598ca0,0x2f8b563a44390421eaadf006ba22c05f588,0x3417ac84d36e9507ff96801084b87bbbd8,0x306455bb8db322ae357f5abafee4a181a,0x262a48772f2becf462af4e980e115c30,0x19892130ee32f4884470adad5ad26c0,0xe7430b019eb69fa8a4d4df9893c30,0x6e2a09f6f8112f6adb0c87b75beb,0x2bcf79167a2ccf62978d8c1d280,0xe5ffe3a2eec5309302850dd84,0x3d388b4b4510a897091a8338,0xce5b10dd4e78177e992d04,0x21242e86f8843fc3e9ef0,0x3d11665a1abe55d582c,0x47f7d8a926fa45800,0x28d3de053b44e1f]
def m14 : List ℤ := raw_ints% [0x0,0x3289e5fdb92a31ec1fbaa5f12e7d8fae1cc67c561c31000,-0x683d484b3ec077e5b8db68ca6bea3a4154830855339bcc00,0x68886c686da7a0e6bd706c2db889266589b1498f30259e000,-0x43e8059cbd05c912a65335b97507b03e12fb6a58c8ce409600,0x201fa5639f341252739a24de2b72ae9b5640e5b946a6776b800,-0xbcb5caac37a4111c5ee2c7f9d0ecee330bd5ca3fe8fb94e0e40,0x37f7f11d6d31e1bf2ca4ef995f4a646bc19a0ceb81ed418fd840,-0xdc7954525c289cb8c5ece0b7eed787a5c1a291d45c3c493864a0,0x2df4b525341b5b310d788b918de14b9c47a5af1ae3c1efa70f2a0,-0x83afd3bb3cf4ba8e39697d71263c83bed7b7d7f194be0123a01b0,0x147ed6a5c366e166d317c863d30e09b6b9f5f1b54cb70dae225c30,-0x2cc05a4ab29093ad0bf4d9784d2350e0239cf763ffbe93e30a9208,0x564a0b0dd6de9a12cff972d3173085927f9482cfa611d93eb4c1c8,-0x93c515d4d0b0ade72d29c70f4bb381b0e56e80e0243965730ea970,0xe1c7d755800eae80e0706aa3ecf0ebdb17d644ef2e5dac85958070,-0x134ed4f1e43666d5653fd2e1ae4d004d6c97d70a52d3219619447c4,0x17ba11395f973d472eed476bead88d939562c1d674a9a2d760626a4,-0x1a3ef2a6c0c86fae349d0ce1856d4abd608e010777924936fae304c,0x1a2d911c92dbd24859cbc8210b541cebc92be457e19cec26e531fac,-0x17922dc10bfb0175b8ae03c23f6d21b1213e152b0d2b03291e25abe,0x132c5b56cca8985e7b03941921dc5bc088452c1025b505526aee40e,-0xe17d8a48e57da31003834584fdc3ad54725a62a7deb9a9f4ec50fc,0x95c00c730bd27ac6fc55583e40f0d8bc8a927b2397ae8c3f3ab4bc,-0x59cd52d1039eacc6ae301b4969add7d3dd7b9c6e09063d2e8bac79,0x30946099d92c258331645500b00af546b2610c27565d60609bb6b1,-0x17ac445f300d4b717bd152c8b0fc80cf479f58c264ba6de1c3bcb0,0xa5f3d1790abb4a71d0ff98565f6f4c63827b1bd8e781227a2cdc0,-0x413857777f9b1daad91998b08f01757a82aa9cafb8e1b8ba6f684,0x16ecc1ddbd299d11afdd828b51c14c1384627547de3597610a734,-0x72e949676750ffdbd17ba54377a5eb75c93ecc7d7de13485a620,0x1ff3dcfad2cc7de5030d70d2629597c0d509ac10698e87a2d670,-0x7d8e8b0cb0c14cc3a1ae89ef7cdab581d6dfb3408d419378d2b,0x1b13c36d075d7323326d977abf0ce0597959c778f0c2766c143,-0x517b55e081d91e819307d648704aa4e26d59941569f5ceb8cc,0xd41d5781bcdcef41d36c0dd3d2b78d6477b923a76125b54cc,-0x1d919cb32c2dbfc1801aec9a39bfb74d81de89f0132ece2be,0x37dbf4da5f6e4dd39fdb4e7349955e770456095dd5568a2e,-0x58262c4bbfb1379d2739f2c36ebd490d800751be4739abc,0x7241e6907177eb946480dcc5156639b165ac47d373331c,-0x772562adb1a158cafab58e92f55ab8f0bd1247d640d3f,0x6164d70708f52f981252dacbc7483cf3e1b8ebc89727,-0x3c6107e3bf929b7273869e938711e931853d34bff08,0x1b31327ae592d358efd04e1beecb3e28fdc4b9eb18,-0x865c2a6069d934e7dca63ab79f6937f12c09f158,0x1a42a5552369faa1c0607266503257e62ebae28,-0x2e3a355529d0474665a8a5dfdf2c5641c2bf8,0x261a2ee4de115edf859bed185cb78c36788,-0xa99372e899c096e2a59832b2567fd759,0x785da8887830af1a2cd1a3a0ca241]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 25 68 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 68 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 59 indices rho q14 m14 14 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 59 indices rho q14 m14 14 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r15 : List ℤ := raw_ints% [-0x1b182aa80fe0e0119491ee5988a2a6cb3ccf000000,-0x24cdfebbfd1d4c3adcf609c23ac63212de87480000,-0x17cfc84ec8315d7a67e39cda31c871e55a134c8000,-0x9c424a997c054f8cedebdced9d4b0ba916784b000,-0x2d9eb12bdc1081ef2751ea40503d739304f5b3400,-0xa176930efcca10bf3d0b63013d4798f1392d7d00,-0x1c1fcc843f8c34a5dfc05e5a54293725b56ab540,-0x3f514889cb01f304674c2271740605f5661f780,-0x7536c263e33c84582972fd1dd64cee98dd3550,-0xb4a98ca98c03b134a72adf3bdb08561d21da0,-0xe9df02dad44527452ae31f2d1372e5e9563c,-0xffc2ea1addf1654159fb3db58fe4a0d06a8,-0xed19785a435ccd582d76aa97d7324262fb,-0xba903b74086c63e4180c75ec510c73a1d,-0x7c8210da13eac410961ac042c9dbee0a,-0x464641fda6c088ae880d81054403bfe,-0x215e8b65276c7bebf51d5884e53f9d,-0xd3905dc4a3ffc0d59c6c47645256,-0x45229aca99b268b573024dac6f8,-0x125116ada39440657828e98530,-0x3d68e74a3d6febb7e034cd25,-0x9cd290b8486f8d9b093fc5,-0x11ede420f924ea186e8e2,-0x14f2840ba39b3f909d2,-0xbc2a5a79391fdd93]
def m15 : List ℤ := raw_ints% [0x0,-0x683c6a5b4de706f70170f6416fe2f8571b5960719a251000,0xd55d6592c527c41f05c81d1fe9131826be4e412fba7154c00,-0xd44dc877c2f96a9b7512e1de86b3005e090dd2502f72a67800,0x88d14f0d59c2670ebb53e6a5f9e0c8beb2af7c3661a73ae0800,-0x4031931fed1be35895e9e9284b932a56827b290056d435ab7200,0x175f0fe30982a59c315f577b66e7af3b05157e25169f43a3656c0,-0x6df30f28e2656320adcb0dd6b72b8b5c131bdc47f96d3ef23c4c0,0x1ad48313537d5cd2d7540e573bc3e5b298a6ce7983440ebd32e320,-0x58aa4596e1c531eed3efd9ccf4ced992a005b6cc9622cc4b871d20,0xfbb07159cfde7bc83613f6c34601265e3a796d3a47a8d8893a0dd0,-0x26cb5dac34ba62ca55f6f2710fa99554dd87ed8e062691af030d350,0x53dd53b9641a3b92db73246d2d8f5be4b5c367ea355749733a55728,-0xa00ca77c90183483a7d5ac5d264775abc7c74025b7ea7656894bfe8,0x10f2f67ac149fbed460f0be22b7ecfb37df727a3ac65eb9e9bf05f90,-0x199d31a8193dfd0c9600c97e2ad013a7261d547f54bf4fcf7455d590,0x22a6b51157697eeaf83fbe0961954d41cc7dadab62e3c01c9442be64,-0x2a15a7408f8920668197dee33116451ac327a770648064d5ce055e44,0x2dfd7b16d727ca07862545c4325020312871682951e1f2190d3cc254,-0x2d4bfc7a0309ba6c3a4384d64f943e595b0223743fd2d551297ec274,0x28419142bdf0b367336bc6679bf537236f211ee6c4885b248432a806,-0x204dc225caf89a27858453ca42a3101ea2f21f65f22b02d5cb6aed96,0x1769644a0e8014c63073a052f14711c3bb53c306d97ef6a01b0522e4,-0xf522e910d3ce6d15f8f73fd32b9184afc5ca1ff2b72c13ff28afd64,0x90c4794f64fbcd26fe2c5959ead724050c82bb4cf1dab6aca72d301,-0x4d1227ef0be13402842d3004508a9b6933625909229666718d0f279,0x24ef0d88a35e029384f16cf879e2a79556d395ee5e810070fb11ad8,-0xfe6b1a8e28df85b5aed7e53a8c2f1db2cabebccba27761a09547a8,0x622aca0ca08c9118638ba3f75aab8d08db6faa706ba02cf2856b2c,-0x21d883e92777d1945efd49a640d275f6e84c3d494e8303b3643f1c,0xa63cd04fe2f485b00ba2d10c47cedd3d238af7f724e0e16236b28,-0x2d3e3b1b462994b6c0a4e4e798a12dec22c249beee9faaeff4538,0xadca80c6f65aea8c65c654557d781e3f175958ee19401deadd93,-0x2496745ca8ae1d63734720d50e44977e68eb5aecb9faf24b09eb,0x6b517173104e6c1e5ed0aafb80df08ae646e6ae0b657dd16464,-0x10fd89f52f871389db98b66c492353dca3bd050c069c3c0d6a4,0x24cdcd9268050b742efe17f500698fd02560de0c3883e82f96,-0x4360f82ff1647d2c2464b17de4a4e1903fb41e2b32c2a9bc6,0x66ca05f4f3bcd1c82c6c62281b390d3eb0290a7f0d3d8674,-0x8070468e548489beffa690270cf870f7851c181ebcccb14,0x80b29bd6aa1f003a73ceb0d0bf6c86d6c9d3103ca27057,-0x64b64a2f34191725282fb5e1ea468f5ed5d9944b3f5ff,0x3b83291b677e109956d8ddc92b599be1ebb0e35a5d20,-0x196acc649b6cbf2a058098c69c614baf4433704d370,0x7664352ef31ae82b7ab984f8d079271615cfd3d70,-0x15a8febe22e3538488725610e34592c5a686a500,0x2365dc5258e7af1e88972dcaeb9ed49b8e24b0,-0x1ad337df2483dc9bc13b30c758911b024080,0x6c887abd5f745f6bbfff996c93f157631,-0x4518061d99597f1993b8b5ec39fad9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 25 70 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 70 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 59 indices rho q15 m15 15 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 59 indices rho q15 m15 15 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r16 : List ℤ := raw_ints% [0x7cdf4385efdcf68433a99e92424a79483dc83000000,0xa97fb98b8482708d802aab65047556d3c1581a80000,0x6d92da264f73c833517162215d2d39619cd460a8000,0x2ce6ecb97e1fc595002273619bce70f193fc9077000,0xd18d07e0d9fe5eb70780cb320363bc50f17fca9400,0x2e4ea98985d8c7ad28485b0208929d0ebec0c2dd00,0x80e9ee997cc9ff6983e600518baa78137d2039540,0x121e272b62947acd9d4e2c465a9e93504bd3eb7c0,0x217f0e6c073630d56a6104ef420a6da5550b3010,0x338e17a44cb8c2455b688aeeb823f80dfea09b0,0x42a2d2b8e897539f404914588cf0d7e6f8bf8c,0x48bff741ca6b808e3b8d0aa486554db865834,0x4350f88ef050dab06fd5b4adf3e0a0bdb80f,0x34dc20601cdb98890bf31a0856bb2ef1fd0,0x23329657f27dead4baa63544836de3eed5,0x13d0f4240e53b35defce9d6a4a06ae19c,0x9621cf1e2cb5ae55794d44827f51f6b,0x3b4dd777f23791f6948ce7cce473b0,0x134fa3f40fca88cb267d75b0ba8c2,0x5188a61799b4396ba46429b842c,0x1101c10d5af4c67caa2ce14189,0x2b34086a631361538de06310,0x4e8cf4bcc412b290ac79e5,0x5b1f4a8325a413915d04,0x32ba9ad06072605ca5]
def m16 : List ℤ := raw_ints% [0x0,0xd6fc9b5c50ac7e5d72f8fbe6f6c42033a86856ea4dec71000,-0x1b4cea26dde179e2a6cf3e60ea5b761cfe88166727089becc00,0x1af55a7f54d3d1dc1627dffd6ff2bd10862fbd44d8c64477e000,-0x113cdda19bb7d41c8022793896f812d93e25a03f10f3d6f6a9600,0x805e9665a391130e3c413cb9c3e4bf6fb9e24984ee40df8504800,-0x2e5a1d97b617d8b52e944df5d51d6d1498ddb13b2f4746f68a0a40,0xd837fb7bbd0585fe80e3b1d4b14fb93b1eb5c057e6377c95df1440,-0x344dc18042849fa30dd3d3099bf04cea32aef700768d38e19ee03a0,0xab4d470d46a84f9c4eb357557a8454207d3bf16e75b5cae6de469a0,-0x1e1c9fa19b79f627c8b86cde34c4e5f5b026f15a27dfc323df9a73b0,0x498e7e2281f60ace1adaadcc38479fe4f191823ced8d117bc2374e30,-0x9d750a92756c9d9be2ce11cb40430918d58f17892244034ad89610c8,0x12976911d3c24c899374db9969015d41c8229e4af32f0c2a45f6d6288,-0x1f2c3cfc7aec35328e86c0b8ed850884eb61cde7aa6b06b41160564f0,0x2e9a29149ffcb3319c1140c9a0d19c055f1dd3259de45596fafd903f0,-0x3e57a3ddc5bbb2284cbf6f4753e69a5250678fe20765d02b7f3f20f04,0x4ad7e059d5b612c4583a807d2c0ad86b403c2bde71626a4f823a877e4,-0x50cfeb50e5fa4eb99b9571edf184d2647ffe0abcfe6909d75898ac44c,0x4e9bac9864530ac99a9f6ce12fa012adc664aefb7083c66d0d603abac,-0x44f65717fbd9c63c68f6a6be705c7fa3c0d2674cba2c7a83ec23e9eee,0x369986f559aaaeb98fe7d3b9a57d31113679159516d8ce4e28f7484be,-0x270530399636686408c4c6b3e77d1eef2638cbe52deb8f1e754767a5c,0x192a6e695a4b3277db137713ff2daa3cf3ee279fd7fdc4e9a11f4081c,-0xea329ca837a804ae879834fada99695721db6f8bcd69b705bd4ec709,0x7ab6db0c3a1218532ff5bf7775af156cf7c80a0ab42b3b52497875c1,-0x39d618b9c2458a9e720940d504f50dcc7c8fd01af8aa36494b65e270,0x1878403bf89a11a508b3e8a92d53b4fd615b908c041c1946e46ab380,-0x94530746843a817e0eb666aebd3c0093f8fa79087f6dce5ad159cb4,0x3229b6eda0b04e66badd1d610399e1a9334a1f5c22da2ad15a1d3e4,-0xf16da6406784dae7090e235b24df7e26afbfcf08a64333eeee6fc0,0x404ffabf0970c1e5f8a0dbb81040ab496d3049fe57b17d94095210,-0xf17e5aa3e7272d43e20a3f73a7ef6b3dc9bc790e5a5d63bb6b13b,0x31a1398178c7a70d5113b1700a19688be657eceaa9c6e710f33d3,-0x8de26197aa3e7ea9cc3a30384879085a08c91e8b309fba68554c,0x15db0eb66186b0935f2a74ed774e8d4e3e345d9fc8da6062b94c,-0x2df940226e451f4a247d4ac9a228cea0f799d49a139e850e9ce,0x518d5d70ad6526c73c57e11fe04ac076da1d62d2868488aebe,-0x783f20ab8b5c7eed64f269399b8c01e6348ec948f88f68b5c,0x90cf1a740d151fed14258308af682a1a349dfa0bf28931bc,-0x8b6328c38fff40a4ed2885428d4632991e37a0105aa4a6f,0x6862edeeb64f958e02262dec0c892a6820dcef515b61d7,-0x3ac5afa878fcd61d82225030017635befdef49003aac8,0x17cb4821e71f73a43ce7cc0009a40530925336cb96d8,-0x686e7ba34f53ddcf713549b7a66d0fcc8cc9c03128,0x11e072261e16ce22a29395f483078a56249451b78,-0x1b1c7078bab4c267ee3c35810879511c72e1cd8,0x12e24822f3555698f2641ff909ced87446668,-0x4572a75462c7cde3eb53bba77ad43b4549,0x27a769e93ca164b8853cb926e584db1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 25 72 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 72 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 59 indices rho q16 m16 16 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 59 indices rho q16 m16 16 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r17 : List ℤ := raw_ints% [-0x21aa4b016f24e114211147ec6f19c167bac7735000000,-0x2daa4cbfc3e47544eac7d355c93548eedaff19c980000,-0x1d7fb2d5d9dfe9a0bbc7178747207dd9cc708f1498000,-0xc14244be7dd3fc177ce371d0d49025e1013d45c31000,-0x385229cd4482fae4ff6151319b172bc8a8bb1c3aec00,-0xc6f38514ede97267c69559a69573dc855288c45c300,-0x2294cd31bbdc3ddc43345f3008945875369e1325ac0,-0x4dad5feefbe69b48634f08347b74d774e57e70c5c0,-0x8f70d7b107408bcee2f4716d46a654aab60886b30,-0xdc7d7191cab137473ed91dee8569bb56f07fa8f0,-0x11c96e9e72b28e3193c0cf154086acaad15a5d04,-0x13639d489c129f0cad6cd2ac37f0905a3af3784,-0x11e9358b6a05c2b0b93dded2d8e39718c607ed,-0xe09e8ae51ff00f0bc0788bbeb0c78d31821e,-0x95439cfa567e320fab67e6afb25c5c7e08e,-0x53d910f7d13230ad9ee949eb16c1abc9f5,-0x279ad4ca13053c685fb85074cd8263123,-0xf99ebcd21462bef6f4cff353dfb5e10,-0x5108576c96cfdfa6b1afeef39406f8,-0x154f12453401a402542d1dc0300ba,-0x46d6307cb9409dd340ee20e13c3,-0xb325175c6c992088ae048094a,-0x1440b3d009ceca420a967b56,-0x175aca35874bd0662eb2a5,-0xce964fa30267c0ca15d]
def m17 : List ℤ := raw_ints% [0x0,-0x1bb69006e6663c4a0bd21878c5cf4826a8b57334340b7a91000,0x37e6630e0e8fbe98c62c55e77dfca39bccf8ae34c081c1984c00,-0x36ca32a55bfe2649d8b8efc12f201b5a9c5c115c7c3f5f6be7800,0x22c443f429e426c09403636c771c4d923a39b78658879d26338800,-0x100e11520c0faf011dd035d5210210b2e3f35a0430ccb3d7f004200,0x5c0200c402b01b1517079e39555e02bef79d884e2ab221461a982c0,-0x1a9a2a10f9cbfee7425a9fadccf7a65895f5a102f9a781d75bff70c0,0x66159e3ef440937ccec2d70fbafead5ff4fd2342c1e2df3475661620,-0x14b67ebc22541eb173fc722bbc173cff10ca25c756877653401350820,0x39ba77416a6e5a4f64ba1e5cee40efce35bb9f48d95b1034d7223fbd0,-0x8bb3ee37088f1ee91354eec4eeaf4fe99dd3112f37b2ab573e33e2150,0x1282c9158dd310b33d14dbbcb0d6ea52286e3e5cbf92d8ca2ae30496e8,-0x229f6bbbe42f5eee7fa6b0154a8ffe2ef77c180168ac6bbf93c07e79a8,0x3974f9e16e1d4e06602f5118f52a06a9497bb87739783ccc96065c4810,-0x54fbea8b4e62097be6e61cb9dfd99214c81218bba5725e5f9ccc53ae10,0x707049929b7d91e0733ae77f1c2cb3622f9b046ee016db9221623445a4,-0x8572c3a02f974b1b684cab96536b64d06f9ae7afb749f9243ba17bcf84,0x8e63ee143016ea60084c6db9d26a6dd203c3f75295ff3676521effc254,-0x88cf5b0490c9f9f29cd93b64de00ecfd208dc23677a461caa13a06ba74,0x767ea1bba6a653fffbfe2cddcc5ea7e9f335fda5df8c3bc89ace0f9776,-0x5c92fb0e3d42767c1adb8366ba59c9f723bd3936f36e1c387d8c496786,0x413f3dafb69a3600c754f8eae08f57a770b9deb7f7b5d35fa447612884,-0x2979c1d3e15d71d2fdb48c4f7fb77adbc2a84bc56e87379efdc1f76f04,0x17c305b603496c06fa1a4bec4504b5cf0aa8a95f2363725ba153afe791,-0xc415d33e113d5b86e5cfb2f3b524f0772e9a9ef7961d340923bfa3389,0x5ae615d0adcef1993ca4437aa7f0afe549c4e9ee433d5353e709b9618,-0x25cbaad94c7344b656ec7d8843fb5a8ffe3d239b4b7bb0924dae47ee8,0xe0f44aa4acb666519efcc96157c4905f654d78ae1ee2cf9733ce921c,-0x4aa15d8c70d9bf3a5b66a8b2e92fa01c9db0a39d2bb1c533c6d97e8c,0x15ff98b968708f242c283c2d9a2cd765ffa24efc1be035deddc2d788,-0x5bc54eb08a2a0da461b92d7ddd8d34a9951a9dff83379fd8fad4998,0x150db0a1716ed90ef6cf29fa3d72da28a053b0470bf5b0171b94823,-0x4393743da881b42f4485757340d03deaaa8eff580635e6da3cb6fb,0xbc484ece267d54c6e4222f1fc83a3ff2ec960929272d04fb89de4,-0x1c3759369f158286878d9f4803d5e460163675c150a99e6b20024,0x39a0ff5a02f998f0364365baaf73f95126f0327b1fb632d3af66,-0x6309354238486992c339235c0881a2c8d9fbce7a07e6b3e2b16,0x8d1bcdc64a2a961efa87f71fb8da1f38c6ae9666a4fe6b28d4,-0xa3bc41041fad43c42703fa8ab5e71d8887a8a06389939c974,0x975aae16543c1df1fcf2c41ece1ed1d0035dff21dab3fa87,-0x6c6fd4f6a577a2483207e47b9d4a6f0f0350fc5444c8daf,0x3a260ee905545db367b75bb46eead497029d98d8a5d660,-0x164e7193d7dcdec75c5c1d18b44ef6ce6191f43f688b0,0x5c356dae222a362c7b3ce8b197877ce6fedc07b3f80,-0xec32c2b7553864962d9708ff33332bc032013ca90,0x14c494f465c58acc8eca6708d6a8d08349a2dfd0,-0xd4ad09a757967f0e035e66bab2fd1dd2beba0,0x2c6d83a10e62a6cd62875b330f05bf55aa1,-0x16c0e03a47a4907c32383371b64120c9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 25 74 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 74 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 59 indices rho q17 m17 17 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 59 indices rho q17 m17 17 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r18 : List ℤ := raw_ints% [0x8918e97a3d7d46b47d3e8247022d4da3cbc79d6d000000,0xb9d927bf297de87afd9989cdf62423411ab7fb66d80000,0x77f8f5c02b4dd34a7a41e13c7d5f7c5a2351e5135d8000,0x311699f4683f6b0608885712efa653d5b8814022ed9000,0xe4b5bcf1b865f86a015a1f53aa4fc8367c74138deec00,0x32737f24b93f87f4b1faad8a0d9274b61f1a489175300,0x8c2dfcb6e35dcf639aed6660af9cd852c0db605b9ec0,0x13a8fa4d9aee7f9d881edb14ed8b30a7018e46d54840,0x2443fec0cf5328b21503bf2364ecba04bd12b0e9fb0,0x37ae2f2ea6cf6d83031ac93ccd9e8da6797c5905d0,0x47c6a93f72786860e1eb5d8428ca41c1d7d093ba4,0x4e2221913d803c36d7a6a57399baac6ac55e478c,0x48114e7f583b77e9b1189e9c03ec4f51a90aff5,0x3864b9cf1d8c13cab97f107051e70323937db8,0x2568150da654e797b895e034361a00fe62690,0x14f88a51fcd68ed71836aa73e4208eca35ac,0x9e2302aeea4549a81fd1af5d6cd1e5be72,0x3e243639e074787740a91ab0c24e082a0,0x141e21d9410ab435504a211ed274a658,0x54631a0e1b1b5bf5c45ed78f12f524,0x117914a61fba838cfbffd1090155d,0x2c04a52752b8a7d32a7aa0aa398,0x4f458bb6cfbda5ca4f7a3b02c,0x5af3d1a535ee4bb4ca7d8a4,0x31fd9df8d731bffb83914]
def m18 : List ℤ := raw_ints% [0x0,0x3928890e3b32dc58b861527917fb84cfbbf63d9bab57accb1000,-0x727aac88c7e5df85b4fd3baca919117156c0e74ccd0b9f4a1cc00,0x6f6441c57fe0395c4da81518e05863e56937801bd2bd321495e000,-0x4627f431b4741da2caf0d988ee7057858209daa933a079031f49600,0x20262cb72ec6827707841528489117f8a2152d3af4965a80db7a5800,-0xb6c9950da68143e191b5d276c983c5948561c9d6437d80a1f3526640,0x346b9947685a04e72d1390edbc6ca8ccc9918c47a062cb5a111aeb040,-0xc77a7195e86ba3b76577db59714f1891a8551c632e27c6913c1365aa0,0x2820169452530ac45caeeb5165b430e6907defac64c8e520c28f75d8a0,-0x6ed6c88ff2132ce34e878b4e66fb2820adbf4f0f2b6ce0bfaa516bd5b0,0x109c5a0208fb59b3569afc6362ad5df5fec78d8b2021f5a934fdf743030,-0x22e1c797017eb027731f45665e1650aa60cf185b9ecdda48e7794168d88,0x409ae52b605308a33e0510f6a24704b1a53a09705b344265cd4693fd148,-0x6a20eee81df25a76d44585f4db736e311120ca30954e3c5d9f2a6edc470,0x9b54ab85d2e2cbe09510d557a9a94af32d04404a5fa181b3d541ec6ab70,-0xcb48681adbc6c0707cfb8283d4e3f7494ffd430796b473663832f15f644,0xee8e1002fae3ca9de243f304c9b9890ba712ab4280c3e8ba1acd1674924,-0xfb920d2b69733469b59e83fa8404db933988ede9124071bf1189168684c,0xeec841359a77b09caa62704b88bb9a2096e19616ec67dd23462cd6ea7ac,-0xcc359b5a6d55700c5c9b4dee6b7d92e593b3621aaf0ab10e0b0278a7c9e,0x9d723808b257557c2713695141c861d643e0ce82cadbb096a4a552d82ee,-0x6d73c80ad9318fe10c75fd02205a5b734cf7f0be2b3a60d48cccc9000bc,0x44953e0c245506ec44b59db4b3ba8f26caea266bd9f9b34053663f4587c,-0x26b4c71b988a6d7ecc7416eddaca39112d2238a085e0ca4045b22c3e599,0x13a6cf1ac46a0242373674360ab3b218ceac1060e2eb1e6b0546a4150d1,-0x8f5ff6c9d78500bc55a4081c0a91f749047dd5ee273737b9623bad8430,0x3a9798eea35532a1f761b008268c99d39c07597725aebd99b5c2f60d40,-0x15671049ee715457b442d1c40bed24b22ea62c50a0d889c4b7b47def64,0x6f72db14c4244a40565e4c58ef810dcac1b2a6266eeb80e5c44b69114,-0x203137dd9d319dadbeb434a7bb787774ef4d26d60a864135e8b012e60,0x837278ce5944e4e61e5b1c33d6df7e0e56a39e63ffa17656408eeab0,-0x1d7a414a71a5d8b57489ab65d49c1561ff4b7c435d293cdb50eb964b,0x5c5a7eb388da1d138555cc8a6b1947392050b0d49d7a62cef7edf63,-0xfac3b1b48b61d86cefdf478f3f1b4e609ab764e6b55d3f46a271cc,0x248e942fa66c4a1cb5d0cf0d96882f6f00e02932e71499adcf2dcc,-0x487c4c7190b00ef5f1e1acad8680beb09ac9e72ff41ce4a090b5e,0x78a8747854886dff009ba06f0361adb87f83ff07d42465de39ce,-0xa6179d292ac3d2be11454fb41140f920827a495cefe24ad12fc,0xb9a6698a0dfb50b5f9acbf270ccaad324417a5f6b0caa5375c,-0xa4c1a8ac373727b076bb0aa3c9586a0b6cfe71a5c5e8e119f,0x70e2b23d5c7e7ecb04e7eff96c185e1fe3687c5832121e87,-0x39a203fae07a5b1992353f8017e0b26a7b16cc0d3c07a88,0x14f09c356e0a7336a704c8e202fb9608876d4c8212fe98,-0x517dafbb3b4fdcfe1eb41a46dd8107ef079420ad4278,0xc325bff3901a44f44decd3e278e7ea3b522dc01648,-0xfe93cf91b94a145eb00df584834a20d70e1c00b8,0x95af0bc3ca4866a8f2c55488d633e3e7322048,-0x1c6a494d43d0530a631c85a99047518b5c39,0xd0da77098f37ee56ba0c2f0d2c280a21]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 25 76 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 76 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 59 indices rho q18 m18 18 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 59 indices rho q18 m18 18 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r19 : List ℤ := raw_ints% [-0x212ce00e32b2d9503683441599b42fffece0d62b54000000,-0x2cf2225d23eba8f46de1a887f770182079f87e423d600000,-0x1cfefc882a9dc4ca5d18ada9c6523a9bac8fb99233ae0000,-0xbdb26623f0df52750ab70da421483f80b8413eacee0c000,-0x3732e87710c0910e9ae1dcf6ed26a33aa4401cd1f39e000,-0xc2ab00a13138b149b16af4b51a8240cb07752da989f000,-0x21c6e30137fc47130429272bb67477e02716f245206c00,-0x4bb9b91188b347673f40135b3109e3010cac5b72f4d40,-0x8b8c2405746424b58bfaef9f0f8b1aee960315fe7b80,-0xd6064b241317d0521888620389cb4de4a59254d4450,-0x1139288e28f15c72020932386a2721e7c2de96a3f00,-0x12b9a03d79397c1ec16a692fd6e08a832c9594689c,-0x113f68902ffd9b43713c0216aa92bc050e1882d78,-0xd79e9e23c4d3569911eaa9d46266e98d51ae33f,-0x8eca033f1ba60d76e274d30224094dbdfd6ac0,-0x4fe812fafb55f64bd68124185b0a5e2140998,-0x2595dffd1345c345d1acf5c20d3c765e10d0,-0xebcc4864821cb9f689f977e180dc4700fa,-0x4c2727c1d58693d7a43618e210be85c00,-0x13e94093f5248b1e24187140936f2d98,-0x41c416d03a3f3eeaa05dadad40be18,-0xa51ebe732e5cb32a4fbfe45ceb6f,-0x1283b041af8aca4b39770efe100,-0x15268ed98a7bb8802d8752efc,-0xb914b521b62bb020253560]
def m19 : List ℤ := raw_ints% [0x0,-0x75e39aad5a18e676fc48ba19c176c1ec73abdf111164d462d1000,0xea7c0451b004e9d8fdcde0128743b3f9c2eddd0e66e7f888db4c00,-0xe28ade58fca87216ec30aaa2527632468e0a170eb6738a022567800,0x8da3ae36d169ee8cfaee17f6a6c2d4164b620b1d2474c25f15390800,-0x406b65392b60c045b866a593c41c9cfa9975bcff81b8f5ee1df139200,0x16b6f8d06f51d8e91bfeb13bdddcd2805d7d46f309786845871a9b8ec0,-0x6765e6a8d38885b4da9b4b48c1bf0cdb8643a5ad88de284a17329bfcc0,0x1863dc592edba982f6e2d8472694eeea86a73c8953d9b16224dd55ea120,-0x4dd57b592c7c04861e129387292741490a8760c60e40bb50031b6268b20,0xd52050ef3591528435a70c86d8738962e21d26f18870daade33c2a039d0,-0x1fa6f236194e6ccf78d4d55ec299559b7f47e9f650e939177c24a417bf50,0x41d976ad24b0d25a31e9970e2a1bb0a04f1f7b0eda7ed06e5ff745355ca8,-0x78c9337a973a8b20a9bff280eca7e1aac1cfd0bf9dd43b456f1c2d154968,0xc47108a2d548df484cc48af64a29cc6f9165f940a38db97cc517ad898c90,-0x11c8bc8f2dfc6556bd948f477393c45ab58d745588af0dd7a06b72d002290,0x1706761bdfc137f40d1652734da2a6a55d39ece9c24a5650776632b26bce4,-0x1ab86e43507cd84cf91af4ed325faf728670779b576ec9a7afc54701b10c4,0x1bda789dab4245fe4c672219a3df009d8911d030de1ed114b0b579575a254,-0x1a1edfbd2e21ba1fb551faa3f089feaf1aca031ca7b03e4a37ade73577274,0x160f59cf5cbddad12a0d7e98541ad88bfb58d23c04489adcc3c67429faa66,-0x10c98829b8371b1c7feda09cd7466f1524d4cc8c76e1699813e54de8bb8f6,0xb8304f36eec475a4ffa4d836ff4ff00d68dc3b72495596be004b68aad124,-0x71c74e170f2a17b2b994a7410d220b084abbb07a3190e9e572c181e893a4,0x3f431ac689a2f603f91d3be2ed6130b267e9851f16c7f62618880ee09421,-0x1f9ee8fe75fd0d609f3db241261d669dc2969db92f083d598c5048548499,0xe2f238c78159411d465ef9f466eede43eba2ed96fdb4f1991e8bd0a2158,-0x5b28ce86a4f3ef563e85e51fad611664506f1f2895e55a429fcb253de28,0x20b320b15d5a2fa40e00d5a59cb1b2aaf740e5fbb517f1448780da7338c,-0xa70bb679b34189b4a71b75e69574ea2c755da930c32d6f3aaecca36c7c,0x2f48e24477e8030879e59df091a2839b101b2fba8f9ff75e4bd9a7fae8,-0xbcf9edf9bf70074bb5d1aaaeddac9deea73249df2644b0708e1b4fcf8,0x296cb5088ee0ee04269fb31f6d68141f6e9499740f0a0a1d3086713b3,-0x7ead00898b7b3dd42d453b38a3096fe90bae0d9affc7ab3a2f3ebd0b,0x14f2c62fe5b72242d2fa4a59b39004a68f41448d642a26ee9d5adf64,-0x2f870244bc6bfcdf512ba77518763b1587c0bf36e259566c91201a4,0x5b79c6f12a874a38b7747c9c4da85755fcec9f9f66eb0a318c2fb6,-0x9376ea9b91d9ed1096e3af7daa97e21da5e2ff216c9eb016596e6,0xc4130c3eee1d530f60eaab375eea7699fbcf8fd33e096d1c2c34,-0xd3103789fab957a9fc7df91a37cbccfee9d59a576d7b603a8d4,0xb3c617197b1693eaacbd6db2234171f1983bf7f6c7d5fc92b7,-0x75c1e02c3bf4dea57d58d4ed82934a086cb77277dac457b5f,0x39378c3b3cd380f4ee1259e688c0e2bef639e1cc2241e7a0,-0x13ae90185f2ad5713e0a527f5d286d4111983baa7ca8df0,0x48147b927539559aeb670c2f682c3904ed7c767430d10,-0xa14dcd62a52084358b99fd9c40f144f09e53722e7a0,0xc3103d3bfdadcd5e26729495be0fe782926cfc3f0,-0x6955ffb6dbab4b7d5e4240e41b2fcd15ac877c0,0x122b6f154078c64f72fa44d27d3b565b60011,-0x77cb18042f42a7a592a8ed56fe1dc2fb9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 25 78 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 78 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 59 indices rho q19 m19 19 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 59 indices rho q19 m19 19 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r20 : List ℤ := raw_ints% [0x7ad33b45be2b4e884df6e8c92a3373e6f9b5eaf0360000000,0xa65003602940e970187403f8a4bbcaf5b362f57b3e9000000,0x6b3b1bd9aa2487d96d3fc305577f5a7a80a6b70ff87700000,0x2bd14b983b6f169411fec00ec40dd71cbac930f1045c00000,0xcbdda6130c6cdfe756e4717943ecd5d640fb5afc978bc000,0x2ce71a3f890822b5ee71f185368f8eedb8e32ba781e94000,0x7c8f500c0cbcc4200d9f74776e42d9fe1b8aa5035de9800,0x11704d1f9980462db8a1da2bd0ca2df9cbb8e129d8a3400,0x201b5a491175625172f770f4993a8274d85c0cea9a34c0,0x3131a8c46240ec0dc2bb7a09983b37cae8a8213d86480,0x3f46000f6ced100b69279c9a9ff9eb85099727014d30,0x44b61b3978185411a6dba01868337ec8a4aec1cff00,0x3f35f2dbcbc4193a62ffd8ad1fdeebb67710515544,0x31524b131b6bd86ea4ef31592caa34fdeaac866e8,0x209d0c058be4c1ad064e471f57cbe2300592cd01,0x1238a402e8c6c642165684fc734ff1a05ac1000,0x88e30ba85c583baede5b7842da323738d9c88,0x35919a47ac315f14b69c0519abf21845b5d0,0x11435da1200a637b5fabfd4ec79819afa06,0x480bcee583e0ffb34dec4c79113cf6c80,0xed55a6708a903fc38d4b6eaeff43288,0x2521d5541f2357229d31e6dbe80d88,0x426505a48a40d014b3a8ff1d13d1,0x4b9046e969c80a305b8dd2a1c0,0x292689dd7adc102f13d946e4]
def m20 : List ℤ := raw_ints% [0x0,0xf3256f0589d35b556855ffd51f04eff7ae927c1333dff60bcf1000,-0x1e05dc9d7a27fbbf9fc7fc8230bfba333220a97edb43e709a444cc00,0x1cce185db4829127173a6b6e27a2371e878b3934baaac1ce852b3e000,-0x11e193e36e919c7364d835e20eab77b726b746cc389bf431b92dde9600,0x812a970d6785a1332096b7b3a9df9408b8b872566fde74284f3018e800,-0x2d33529c7082c9d67de245d9c647099e0f0b87e4bcc67fcb9ad2de22240,0xcc26639aabc4a31584b86f3643811a5af939a182a0beb47681e81e9ac40,-0x2fc4d2585f2ca49c0aecf8b0a9ad385804fd9c85042051a9aa57730929a0,0x972cfa0c30eb2a0d14610302f3ab25d7008971fc218ea4bed9dca9beffa0,-0x19a67b8d5d0b0f8d5e46704202c530a31de3906cf5f787647a8c08b22a7b0,0x3c693934af6fdd3c1e7a9d6917bb2b8c2e8a8728e0dc61666b154bd3d8230,-0x7c8768527e8e95306ec10483cc9e6366423dd3876b7529122e1c3e7d7f848,0xe2415fb11253066021a0ce243be2c41133e87a63c4722404bf8d76efe7e08,-0x16c5c5fff74ddfc2367f446900c903da5fc21b009ef2deda76598520a1a7f0,0x20a6839f2ee0e5041700ad2ed44906e7b08ee57dfc71f57ab8f405f3ae56f0,-0x29d39492b4eb75fc4466e754be90ce220610648751963fb829230693b79d84,0x3001bfe7cdc4e7a24c0e0482a588b68d5befb16267220cdeb6f677d4683a64,-0x3178da54ebcf7708eb3a4310c90adeacce42b7d4455458721f9ff2fc109c4c,0x2dd81e58a8f30c7924dc3360cbc5f403dcbe4220cc7d2ff01026fdbf9a93ac,-0x263d3ab8afbf84b01f22d25b695afb7c1297e738400e90423f619b75efdfce,0x1cb979abace5c4ac69aadeb70e8f3cff24aa61d4cf816c7e1190c036beea9e,-0x136ecf778e177a9c8e1dd1927b7cc01585cac824d1eeb32c4297f892f13c1c,0xbd5e0b67c32fb90b45801e57dabd039530521b2319f094646481744a37ddc,-0x67bdaa783b12edb5dcbf9cfe1c0e4274baf8e3e3c9bcbffb403630779f029,0x330db74a60c30debff1fcf0e67c29ac2020842847094b294a24c5a795afe1,-0x1687bc32512be1d938724596beed0be8392287b4e9127304459deff47c1f0,0x8e550b6c4894ced796f3678bcd8e6a39eee7ac40eee6e216364c517a3b00,-0x3223cb76817d474fcf5e34e5fe4546185900a7ed8855f2909307029c4294,0xfb49ba6952bb7f45e15f08e3d95dd3825cb83fa595ee077833101cd52c4,-0x45b4d56987606decb99c178c85fa59461920ce36d23b2e004ac6e03fa00,0x110acadad86d7cda330336a8f025a296981e5225b635ffc10dbd890f850,-0x3a6cb4fce31b01d5c37c9b939fd97221aace132221bab8217f5e1d7c5b,0xae5fcf28b71c4ebcd374e33fbdd26e5114b437b2b5e5c055c9b9083f3,-0x1c18f7bd823f2133e835c43c46c67585b58e85468184bd77714810e4c,0x3dffcd005bac98a04bb25b0326102a7f6b6a130e28c031a9b81c324c,-0x73d0d2bec5c4dd305ab85a5fceeb6e7aa0b4011114554193eb9db6e,0xb4c798a89813a059bfabeed757a828d36679edc449f94f56571f5e,-0xe8210b8206b17096bd8c10deb3a14fb7ac924192d6481bb31399c,0xf09401731adf21a0c41579dafb0bfadea41c206770b00c3b4bfc,-0xc49c3b5885f074fef56867a695dde9c1c44d2fb234d37e6eacf,0x7b14691b35ebe28fef67192902c859e4234df7bb81874ed537,-0x38e4dd1e5cfe23091b1a33c979c09324ad439195fd08e4e48,0x128579cc060bf922b7b15e40ac6b886072a27c836e734258,-0x3fce481acde93b55e437751d318f02b8f8f1f252d4e148,0x85622ffe81b0d01e43486050247362489e0972d53a98,-0x95799da4fbf08e3ddba2a14eafb00f679dc69d7f98,0x4a1e09c22e384949e1afaf7f7bbb3e6c2f797d28,-0xb9d9de21d63aa74f57f393e089e404dd88c29,0x44b2980ef2d2031cbfe58a581be7adc791]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 25 80 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 80 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 59 indices rho q20 m20 20 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 59 indices rho q20 m20 20 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r21 : List ℤ := raw_ints% [-0x1b4f079b44c5c7361d2c225cc66a9b7952e4db1fc7a24000000,-0x24f576f804f40fe77ab90bc6b09492c01269e3796e047e00000,-0x17d101bcbd00daf1149145b7d99c8e1f3ffc6c0525d94de0000,-0x9b9f3d8c4910bd57ab1de8d36c9386c99ceb6f1a783bbf4000,-0x2d397f8c433e3c98308638995f3de5398cd2cf7cd8e9273000,-0x9f44c868aa4022dd166e4e9c64c7e3e984a8b770f3aa90c00,-0x1b97d5fa6eebf8e64df6289304604a57a25db3818eb3e9b00,-0x3dc2ed4ca28ec1dd8966a5a7e9725641a9b65c3d232e8400,-0x719d7e81b728b4766401877ce5d417e1a8afbde67ee66c0,-0xadec4ca7262d0abb8842a70b1a426a38650784edb0bf40,-0xdf7b3edf11dd70a51ecbc9fd5c60a570f8a592ae80990,-0xf26e691de4ee9752950081d35571799efc4ab7e82010,-0xdec49e5bff98388ba327c4d2e8ffc53dff9d7ec8594,-0xad9a605901cf8f61c5a2622bdc18a2e108e0da5040,-0x72a37352642a9c4de0d8f350106ccf595e6f8dc70,-0x3ff45855e2ae43b3d45d6d408d74297acb6ab6c7,-0x1dfaee3839fbe1d27cc5b414f2d12c6808524ec,-0xbb62d29890685ecf8bb1eb443b0be31566714,-0x3c452d52fc211be30ab4341816fbc87f2f50,-0xfafe9b76a7cfd29f4f50e7f0d0cd163baa,-0x338df3dae602f0cf6aa671c725aea902c,-0x80b7603189dc62fd6d2a5dd4e948bf4,-0xe57a6d740ec00506d24e195e09e70,-0x1044f719b186b525fe545f3cfaf7,-0x8d3c1d1cb2d43003026c3bfd4]
def m21 : List ℤ := raw_ints% [0x0,-0x1f57d34fb6c43ec6027315fa78ffa2eeed80e1fe79afdeb785b11000,0x3d83d722b0e12a7087ad5e0c1f2b700997635d95a43c0c83e2cde4c00,-0x3a9ec877ea60fc8776f31d2fa729f34b9f133fb0adf98bf22b756e7800,0x2422bfcee3c1698a7621d8513dbb684991fa5f6b3c91c22736ea8be8800,-0x10327d1249dcd44a10bd94e175d0b84e06e2ed5f5965814a63e7eef96200,0x5a04792ef16e54aa248a447f945c4a8687c51fa59e604a688e47d5bb7ac0,-0x1937686a8f9a793fa05d3e015d974edb0e39e7eef1d1c8f16d0f3b36868c0,0x5da967b9f9322d9a5538b71820b220290e244a633eec73d9ec91229a94420,-0x126005e615d75dac38edf95c0405fc3b38898628a6ec2a63d79ea556626620,0x3176d4894348ecbded39d61a9b119090dd380ff099b8e4d52d662f03dc47d0,-0x737baee130d9938cbe9e6c4b725a0e6783d97cf18bd153dfe17dc45da32d50,0xebe893fe2e300440f25e091359f102718aa68b8ced8b842b37b31924edd868,-0x1a89f1cb802f858316030c06077d6f6608fe8649f403d9b10e2b033365bdf28,0x2a532651c080c2b57b83e6e32d5c63a80796f6e821d0454a5a3cc8d7a874d10,-0x3c1331434ca2099f2896b626d26962a17188d7bcd7d7f89c12d7d93b1fa5310,0x4c281d3edb22925b3c46759d1a2bc254791ca32f88299854a535fe27f2d4424,-0x56769f818d26238c384d7d067b1692269ab608aa106e9a6d33f080edf704204,0x58194847f74ae2eab2ae51ad117003882f4bec671bfde9c3546a4fa77696254,-0x50ae4268c1669fa4164519f9778da36ec5d071c2ec102a97cd8751258a4ea74,0x4279441548d31352f9c994da60ae36fbc94b99b705aaff4d97d4d2fbc6d9cd6,-0x314bde23cc23fea48dd4a2391d3956738fffd847f5d5735d2fa5ebfeccb3de6,0x20e7c6ae54e92dbae2b1f68c9d602891b980a75d911109bc3fd9dd1abf004c4,-0x13c2d837c61c505ce00d26175bd95964f5cc2fa3f2845d756afda6fb1705344,0xaaada7e196537a5ae8aba53bd2dc9ae64c917508b84a7e070953ed91faa0b1,-0x52b4d82c39cefc8d162e839c36a3280185e033b965b1a37fd49129d3412da9,0x23e90697d65c1aff1609d8377591a5c1764f6cefd3f35e1b599ab4d05e3c98,-0xdf023f7193b29cd1913946ba75fc8a50cea6b4ce8d5504fb955f625162568,0x4d27722016e5b40fbacde88ab04f238e164e37e9ce231a8ab51406deb937c,-0x17b5dc98fca9969b6b3357c0f693031b09d9d403b4d8e61146e9aa978ecec,0x672107e909389e90b61f9b097a3f01fc0aad9d5fa9295e680d6fa9209d48,-0x18ada61236412cd04ed1dcd542ab80d5fd22de7e09095f5c6d483822e758,0x52b1b1150cdb7916667d5dc052300d8dd0aea5f6d9b8c74d28f8880c043,-0xf0dfa4e50e7484ca3153e70531473d79ff2453f2f63e2162adb6731c1b,0x25d0c49273b2a52206cf5a337c77f743843b7e650df6f36ebbfc83e8e4,-0x51253486a4dd53515a2f674bcad5cbf7a835d1273392e80a15c9e1b24,0x9318a49752921ba1b982571b745b2d076f540421b4a64e8b9c42f486,-0xde4862fc9995afffd7847acaf6e5875f6f074fe9c0bff4f3e020336,0x11392ce3b1c45245e724960ab27178aeb47bfa8911a2e20a04b8894,-0x112e848e18a1e4636d0a74cdc6710ef543662372b8993e97f2e134,0xd77f7816a46c3eea0e99215a6b6eb43d660a2adaecd69d82a0e7,-0x80e21119827fb64b1e4bb17038eec67c28d96c524cf2652a70f,0x38a85d2a5c540fb2c44b3a569f4255ec8fe002df78757dd0e0,-0x1172dcb2ba10965be7a3246c90eadcb448a171abb66a06330,0x3885ab1d7e69fd232f2ccdc5f6fcbe8d6a934b38b66b220,-0x6e55ec8551a2fb72247ee6c8d3d47d152effbb1746830,0x728c4abbe95c050addf2c7c7d9d0761e8de29eb0910,-0x3424c2f464fd9a33de57092fc79968bf43819dce0,0x76c94189e0b50c13ba2c68ab2550f5386e5681,-0x27637a9ce4738479a919cb4ae40c95797a9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 25 82 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 82 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 59 indices rho q21 m21 21 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 59 indices rho q21 m21 21 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r22 : List ℤ := raw_ints% [0x5dba42c5897c9de48fdd0db9132cc7945dec9c3c420e14000000,0x7ec9c74ff2216b6cd14baa796484c0a57714468f6f3c20600000,0x51a94eed0ddcb8a65fb3310f61d84b90af891ad5ef4efe460000,0x2154dc06f8d36205f3747ac20aa30a931718080beb8690fc4000,0x9ae3f849a1d16defc321c12f0d1386813c059aec3264c113000,0x22123f74b2233e4d1e9b0e13134d57c0628535e7fcf5ebbec00,0x5e61a68a35d1f0ff16972cbabed9335d5da49746a69084c300,0xd319c28fa62d570432f5c5e62c4678137b3448660dc859100,0x18408feaa2ed556816941d620c1530fc76242f763a61d83c0,0x251829e28041f3b1f977db7b873076076d8cc71719273d40,0x2f9f09632e82e276a67604a0caf4f58c68c4fad9d619890,0x339be340cca4319053b6b4f32e1f55ebdeb34097d6d6b0,0x2f5f83a18affaa9a77847e8a804f590ab1f7c77ad3cb4,0x24e032495b2791def5e489d38dc32117d6660c02b260,0x18521cc214cacfb388179e1621651f8482d48fea0b8,0xd8cc119b01ea539a68b42a0707e2bb84960e08138,0x657ae93e06c9ab437638743266ab16d4f863eff5,0x2794523358003633a4fb97bbce435fd63e38bc0,0xcb538fab1e5a2405a43e218f9351f32914d8c,0x34d1f669a89927f7b5e9fcbce48321fe85a0,0xad38a759d90d65092353bcd71acc1f8bd2,0x1af782b0d72c645fdf3d7a4c4244d8be0,0x2ff3b9e2b42158864b2b4381a1dff24,0x363cae7f11b41e139955d6fbe7e38,0x1d54d618c251d41646b20336acd]
def m22 : List ℤ := raw_ints% [0x0,0x40a523d468f4c178650d5d54998f400cc9d9d21cdafabb5a83bd31000,-0x7e0f6bf356adcdf2b4175c7835899713c83cf104a2bbd9d003c8a7cc00,0x77557a54191043e60d47af9b52798aeb7ca7a52901f5d35067aded1e000,-0x490f8c8c4aace1c739235774cfd572bb4c431968a0bbedcc8d99e3289600,0x2084a62aa45c800f0bc9ff457dac55cc5e9adc8bb389f75b78bdd416ff800,-0xb369aafd3693656bcf703aade1a8abd17a3b3515e15aaab3d16c2dc0c3e40,0x31e1f0f0813407acbe0639562e5d6233b0411bbc6eac80ddb0316dbd930840,-0xb7d905fef918a41e7b4f4cdc0067c11f350c6a22aad776c3e012d548ec30a0,0x23c7bb68fac30cd2e202b29cdb30fcdd9de02b0860738a7b01119ecfc779ea0,-0x5f85852d886515d9114155c9d1f36eb4eda9fa0c52c792158a6983daebf69b0,0xdd1b06bd9539f9c30915a610007d8e1e79172d23e3f3fe2a744418ea9a3c430,-0x1bfac57c972ca4b65fa3d242e610d25fbc3e60b795685d578e90a81d4989c108,0x31e633fa3bdafeeef7f1e1f29d56b46e7fadc2c0e826057cc1376a6d199358c8,-0x4ed29144da60396a7b4c4f009e6b51f1fe9e97d4d100412437b375556fcbef70,0x6ec5cb320c2f1e4c969e69f5ecdea24cfda8b435e773c8ecba3786a214b0e670,-0x8afb862e77ba18039231a1405b43222f1c91dc86e04745b776e80399a4a1a4c4,0x9c1acc58aef3a77dc3f56f4ca3b092311953b1d065e687dfa5041b470aa3eba4,-0x9d495a9e6cea5681719ba99ad865feeda9f0a6092cb7a7fa52429a01e8e4e04c,0x8e5f0c01767afb9b1705652a81ecc926831622c1c45f479d55a3af7f0ca5efac,-0x73e180c4e2e554ec6c3689e692d08273226ebdb483cb7f0b951d7e1b703b147e,0x54d969186fdd52b5a927aa38eb4d0add38e425f4eecdc90d26d50514e93927ce,-0x37e33ab0245240cf41a42110ce26263a5eb595bea4c436f06c9b7d5555e7c47c,0x21190de326f3e9a21b7da0c1d2e17cb8c2bec53262f9763d97ffa96d333e903c,-0x119b6f40c314ba8f149c25229a095fc46545e0e18c9271bdceff8f0aed228eb9,0x866da3d7e5759167d7ccbe05211af48a1c8f7f3077109457a94a114553fbaf1,-0x396e26e90899d03d5b369d49d8872e673602a385ea688267a2aa40d00edbbb0,0x15e9e762d9a9d51b3633b2b5282cadd28c5cfc94a10c8d18d83d3fc2c6a9cc0,-0x77233c6fff15db68380f23b9ca9adaa25c1798ed172a0517054b1db9398a44,0x23ebdafb77ab89b71e872477b49c6e2397cb870a6ec18d28da2d68f39a2cf4,-0x991da8369c4f04296f71d1219605caf48831acb66cac35e5a0aa52a312aa0,0x23dca4bcaa6fbd4f8cd8a55a24c3f2bd0b4bd75b284edf5349f83240712f0,-0x757419ac9a9e594dbae9c6e126ebb49d4cdf337a1a914dbbfbd92222236b,0x14de017ea60e149a7a1063659fff66574683f552507a6a4f67b2be256183,-0x3310a33f8e9e53430595eae3a24719191a9a74576dafc13ca4c89962acc,0x6a8c21ea105b9b6e76213f9766d7b2afb7d0bccc0be8834b4ae5e746cc,-0xbb66d7f8ea8d5c4b738a6f4c60cb4a8552476ce07ddb863aee1d78dfe,0x1121b64040f71b1d18223b25fb36406064623e5035ab322229d5df36e,-0x14806752478f3418f04239fc8045b811757d3d69400adf3a6006c73c,0x13ae5111a40a454d4abbf19fb784c267af397077a918cd62cd5379c,-0xecb34d86bdacf9469ba76323e9ea01aa9e677ac717fab03c51dff,0x87336106d02abc12fba7405f91757a40837e23aeb898003c4de7,-0x38809de8e1751370536206795f4980a45f4edc64c971b630608,0x1074875fc250c70413fb2c401c3f083c3214a1e008c2f38218,-0x321a6a9ffef889817d96c0994553514414d70cf8ebfca998,0x5b4ca39ee4c9884f881694ff115098b3742645b0de0468,-0x57c911d0e144a964ec33eccf8f25e84e5efdace60178,0x24add121efb79405f6986d20dcf81c5116d7512508,-0x4be7ae6cf669951115f54053417dd0eef5c4519,0x16946e08cfaee38f6b1ed57a89f27e4c7601]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 25 84 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 84 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 59 indices rho q22 m22 22 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 59 indices rho q22 m22 22 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r23 : List ℤ := raw_ints% [-0x137715aed79e1a41d40a786d0b1bb6c9f64613ee2e0029dd000000,-0x1a51c9b73bb595c6deeedfbe8d2accfd3c4b0d44ba032b80580000,-0x10f198e02923e4c785fcbf0ca260e8d95df548f8e53538e99d8000,-0x6e990e07c2c03b0ed2a589ddcf29fa7058026965035481ac41000,-0x201aa78ea3acd14cdd3396e2155a03adb7e770b82f38e1364fc00,-0x70ece05e0b33cf7245cc0ce524d2ad6a573ddf4ea357f884df00,-0x1389eeface4b7f0c6e1478dc8e6b8b9ab3c866c3b1cf68edc9c0,-0x2bac324d28321efc360136f33a464fb7c8427dd197bb8697000,-0x50381a273ab00ed24c8b76b46d2db8adeb142f45c540165970,-0x7a9a32b355e5a6ef400eed15c80e198af6fb57430f4b11d40,-0x9d438fc3d197c5d78ab21fb66ac63e4f4b3869dbe14ba314,-0xaa47a063c49998fefa2f6e092e25006fafcd28a964c6700,-0x9c270b8164b903c2317da4062aa44e384927be6b795f79,-0x796c73f6c1884ed0d48b56ff9112fbc54acef4f391fe1,-0x4ffdf5bedc66321f40538fd9fd7a35e9a3d3c84bc6ee,-0x2c82ddf5a05ddbd76b3f70a8ae4631ce258b694b062,-0x14cead9136d93c89cfa9b357a549c582446720b27f,-0x81a7ef1b6087469208efed57b1c8b4b4d2a8f05e,-0x2990258eada5791e4b4d4070e6b11824dcd8c28,-0xac74c38e70b1110ae5f5b31340cb1572153d0,-0x2347bc4fb233641d2b2a18a80305af524cc7,-0x57b183a89fd7d759781b5abf8cf65fc499,-0x9b92c16a6482d9c45437d144be8763b6,-0xaf82bda34690c671c8460d6f9323b6,-0x5ea4c91b4cdb1de15a5399b38831]
def m23 : List ℤ := raw_ints% [0x0,-0x855499e61878cf08506b907e7cb7741a6051415b83a5226aafb6351000,0x1025ecf1d76814599cbf3c3b658ebc798ccfdb1198fa3713d07cdda14c00,-0xf3013ddefa6ba61daf64991fa94b7872c1f0a921009f1704e30d70067800,0x93c93d8b7736d2483440cc23af96c3f3c5d2e1abcca7f11bff32878c40800,-0x41534535436e9bbc79cbaa57ca148cd13e58494a32df28b2ead4dd9565b200,0x165dcf51cf835cafeb3d240540dc6eb541c2dfc44b38d8b662868300df046c0,-0x62c4b9c155c14475b2da4ce7ab4ae366b79eee60ff74d5517a4ba84a88bb4c0,0x16943b7f9eb97a631bf1c253a4d208a1c35000e2024bf4682e83a071d208bf20,-0x45c206105251af09b5e45b4db1fb0c850b78574dff54c3b71b9f100bc5f55920,0xb8b87645636d833d83ae17c19fb1cfb287449737caec12f63d80ac4cb029a5d0,-0x1a7fbdd58306e4f10e4073dc940da5891296f82af08a4c69a04abdbbba929eb50,0x352f70d639c47d481132cf79d02ce524b3d0b786ccf9ed802ba97ecc65c09ba28,-0x5dfe98a08e8c681f3ca565c55b6cc6ad16e1d64ca7fc3a5c68cc4b04bdcfe6ae8,0x93157f9c481e437596f5febf9962e436b2852f5103ce7697098f3097a47b3a990,-0xccb0256cb3062418a8331be1812f1256f9f99f4362477f53fae1a9d9d18405f90,0xfe35e7ad5423651794bb057c32d8b003f1b8351a340ecf4d40e19a9428489fb64,-0x11a83888bcb6cdd17ac23e80d7a351a77395aa4a4d71167a73789405b958378344,0x11985442a06a3e74c485e37b7ef1eae16f01c99823c4043fd189b3bf5037520254,-0xfbe62dda861423170f5aa7d470c6e0e464ac53061afa133cbbd45728a9e872274,0xca92397c5a1a34ddcefd5becbe6b90c39efdf7fc6973e5a2b1c7496abcf990ac6,-0x927723eeea9ca777765e4dfa68afa999f08745f67a56564b8b67b1ed18d033256,0x5f34c27c29b5fa429b698b130373d1e2b41968a839d6943289090c4518b796b64,-0x379b7cf0a934041fe38847ea8ec3e04b003ee7c8861ed6b5e15f098ffb08f55e4,0x1d27849d26b0bccd684ba449735420f15eed6738ce9994dd035bc353f735d9541,-0xdb35bccaacc3af3919b8ebfde483e4c9a400234ba847235f4b9875cf3f0336b9,0x5c27485afb3f4fbd646183effeb7a1cc87a108c4933f4ac3eacb0c12ea7a67d8,-0x2291f7689612603d405df55140583a3737a44a4d54f8ddf5d4ae9790adb114a8,0xb8996c52558518c0d8648791c9152d1b29f621be708fb00871e176f195c15ec,-0x369c049fd01069bdb30dac161cc36d9d4ddc6c1b054603d8e56473be01a03dc,0xe41ef1a0dba6f60c6bd72527791a23a8de52174f6a54e39d4cabd43a7346a8,-0x344b3d645260f893ff7ce907b99a0e855741c316adadf6f801a7fa572e50b8,0xa76520c0e89f348c88f0c67983b8153ee0643e7eb5fc120102bd44f474dd3,-0x1d057b52d5c4bc92dc73bbc6fecafe83d06ad2825cbe3337dc581fa40542b,0x452ec627a35465dd3d76b47b52f490f91731f5a85fdcab9ec9f3b5cf7a64,-0x8c57e29a335a4666afa5fb0493a37ee2b2ddd4cfa20daa558650d4f8ca4,0xef7816bb8a988da92d1f53dbcf805b70765c7ea630031ab961793a61d6,-0x152f786847f81a73855c16922ff610e8fa1f5c3a039c1a87589c1cb406,0x18779491462d283dd2d98ea47f447cda7c1bfe82781f5d5d75c4c75f4,-0x1698a3fc6dd9faeb117183b19ec9394060895167b62f91a14ca02a94,0x104847a322d8d1a6f793f7cb3e3ff5434e32cf5f287bc1f7a044d17,-0x8e11b303db0c5570a802d4550ca45665a5f98a4db15f795efb8bf,0x386c56aacec154709e4138219769f3b5b04c3413459c0e9fd220,-0xf8889a9f01d6b6df35dd0fab8e01a717abfdb463e6bd788870,0x2c70b56564be2303165ca1bbc853466ff4ff3ec308a9c9ab0,-0x4b91923ee6ad6e3c6ea77c465e96c5982ddfdaddc801840,0x4346d1fd98a03a06b02878da0622201e5d233c4a02730,-0x19cbfa770dbcd6731382fba986292619d87e0295300,0x307e3b782920eeb2d6ac93244cdd1fe00da64df1,-0xcf1157c1ab4f9f05727d6b600c8af1c8c899]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 25 86 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 86 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 59 indices rho q23 m23 23 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 59 indices rho q23 m23 23 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r24 : List ℤ := raw_ints% [0x3eceef58e7ffddc7825cce5a6cb48ef980ee5cf0f12460281000000,0x54e3d46722e55c0f45dffcc67852afb9862771472b0eb760b380000,0x36a0226b7bc11608e0be51b2d93da72a912ecf457769bc60e438000,0x164642d3607753285caf4dc861a2da7b386ad03123fa6d3caa3d000,0x676667b0589f39dcb3c03a4cda3f662aa8f4116af8634088625c00,0x16b824739ef8105973999032dd2d53e3b66542fe162c004a3d5f00,0x3edbf4cb9c7b55610a9e50d01d28bb22b84a4fba1e89fd77b91c0,0x8c69e55e26e9fae044b5d83bc8fbdda796704a5631886eb70540,0x101be40cff809740dcd5d3700831f753e8463c390ac1eba54d30,0x189a30729aa072da9d366e1ca2fe528ba4b811083034f83bb90,0x1f888c176abc7a6f9e565f4828cb0cd5a09106ab7b9d8e1b24,0x221d688261ba752a30a57a69b3cac305f07cf7d48b62691bc,0x1f41ad0a741c25b7d1dbea47dacb9f762c5975302a7f183d,0x1848124f5dcbd62beb6a5b10e557cc7445303a15e05dd20,0xffac8e396e028574f15a79467d2bfb8368645f7d3e3c5,0x8e1bb58c15934b6b290225f364ad5e782fea19787af4,0x425961be22cc3a8b059c5d0f2789cef2a815ddae3c1,0x19ce3e7139d1bab70c2b490b3f5e0497044144eaf0,0x842aa7161df869e964fe0524bac149e8aeac80aa,0x223878ab927f40eb676305f13ee63a4bb6c38e4,0x6fd153046d603c56e1fe440a7d67bce86fec3,0x115692e4fe7e5896866e0c9528800e8f07a0,0x1eb1e2677a458c3d95c1c3f7cf251bc1f5,0x228c80da44d6e8b7d73d52e359341aec,0x129532c9b60c95d55df764c59b28c7]
def m24 : List ℤ := raw_ints% [0x0,0x112fe7d6a92792b0125ddda04e13a5f7666a796ccbf8496fc0a67cd71000,-0x211a18c1bebe03937a5adeda4ec664bab26cb3d44b841198de01891cacc00,0x1eefe12f1690ee8700bb7a6688f660fa800a0b78523a704a53de5b98efe000,-0x12b13878f0a15e05054cf3ea76f2026e53563a2e8dfbdd49bfdc4e371d29600,0x834fa9ff32fe5c3c3a3ea56182f599bb042b77ccdf913bba3eaea8a49e38800,-0x2ca59fd5ae1c8e9371232f9c7b6d617d8dc63065a4b94a3d976957651ffbba40,0xc3be14700722704f8f4ce18ec94484c176869e3f9d5f2a4b18e2a6cca905c440,-0x2c6a6595e0801531a850452e59487bc3929ed0cfa722da60ef39c52a263632fa0,0x882ad489a3114ec8c584d3971b7a163fa54118d3bf8f8abddc84e5c09fbe575a0,-0x165b406406db7cf0c2c928199907606d7cf823338f699a7d274ee9772c43ee9bb0,0x32e3fbeff64b80c4723103f6c04209e1f8aecf165ecac2ee1ffbea3ebbb8237630,-0x654424d4c6e3be3a70935fead0780168ba2f7508588bfdbb3a067ed3c6dedad7c8,0xb160677e4460897f5cd8dae9ec5af12889aecbcba98df4e9df3a0df60c791bd188,-0x112ff273dac1fa541255d0a89d246a486d0224ad8bcb8de220ad691db6bf5a07af0,0x17b04c4eb8183492623bc4059f56ceb5e11e23eb32e5fee76c0385e028f301839f0,-0x1d2025cf134e744e2309d3c0b28726fcc07c2f6f36358da4be9ab74214c6489ac04,0x2007e7e97258ecc58988f7958ec6f6baa09c8e03bd30dafe7c93211997fb61dfce4,-0x1f9236d6dabbc72cf8f18479c1550269057a3996f33c7e9c4969ba5297c557eb44c,0x1bedaeb9ed351acb2f812def7483bfab9b420364fa28cc3e9312e77ca7b210f3bac,-0x163158586f70e9a330afe8a033aed50bceec1dbe287aaa2fee565d2dbea4a4dc6ae,0xfd8c0f79261f3d96be8e7b375542a6afe6cdb8a5f0d28cacfa082d143f824b067e,-0xa2aa7bd6128065ccf4ede268cfb0db3d0027e0ee7c22792dcf6bad02be9b7c71dc,0x5db5fdad0276b67bbfbbf891af8adae9df4e7d860e146d0cc1f010401dce05e79c,-0x306d25cb5365fccf0f9aa051add2a33f1c281ceff713b0396b9251466500b82949,0x1669d5966f077a9e56354e6620cfeafcf49647e95e8501f9116015830d2e125a01,-0x945b8b7850f00b9349b2337ea22deeadb3a5b3850e1b6795166291c896c3c9170,0x36b817da474766a9d2af51cf83fa9521dafc8396148f9f8c7d222e66e6be89280,-0x11eff9e7eee01f1c39fb0be987b00cf35eef7690362edc35129fc2b3cf2c05a74,0x534da353d7d66a4b2cbb335ad13e0557dcf663b906ddc6639bf1dbd0cefbd3a4,-0x15507551b7168a02b66d08740a5836a43d8061eedd68e952aa0ce44e5c1d5840,0x4c83b111aef5b3200b174ede92ad392f4e651b2d9a4b35373abea3d07011290,-0xef5fb9c503006dfff03538be9f3089db4bf020e8136559783a6a4e9131cb7b,0x287ec1b06e1856b9dd9f292446ce25bbd25fe036143aeae5da7ac034913813,-0x5e07761aecea1067f3bd7f648ce3c6b20e9bf7a2652917fa565089b61c74c,0xb96de4b66e5a12568343524a8958fe2c8641699d70ef3e18e199c5e7eb4c,-0x132e6397df3e145162fcc21aff8c5aacd2984a542f57822cdff608e2f70e,0x1a4528d3bdc934ada42f1dcba1a76a6a4688a70e3c7c197e29b0884e9fe,-0x1d45e689781fdde3ebea27527b21206d5127057c969187999374ed43dc,0x1a0073ccf40e720a6c929ec091119e11d8cf776378c21cca6215c823c,-0x11f4a44e430014cd69b2058ee5e70b1ee5da9af592bd092e2d07b32f,0x95874044a7b406d44b09f4b9a4f623a77be2492e551f5a704c1097,-0x386a5ffefef6c7e04c13eb642f044cae4521979f17a4340e681c8,0xead2c2d721865ca33592e13cb321c668a89f49ce28e510eddd8,-0x27707bbc46f6f519d925872bc161f5356a964057f0e2eb1768,0x3e90492c8918ea1aded6a429d15c198dea84fc7036f3cfb8,-0x338f1e9335a61c739e8fb992f93e51499f3f3e7a8eae58,0x1223ea7639a9749acb59ea24fe90e06a2d7760eb7fe8,-0x1ef94f92e3dad9808f5172bb325eb062f0228f709,0x76a94519c573308578d9cee5497f6f8080571]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 25 88 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 88 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 59 indices rho q24 m24 24 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 59 indices rho q24 m24 24 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r25 : List ℤ := raw_ints% [-0xc55044dffcf61b5bba323f413a09b4c0fd665214b4465423f7000000,-0x10a94695097465c82df8adca9aaadc4129d0c5be97c78b92121080000,-0xab781b146116e928188f93c76d8bcf3d4f26b67d8d2b5d2f9a108000,-0x45e36a0f50b9c114bb87e33802334de2dd10688b7646c8b3b438b000,-0x14446202bd7a63fb97218e847e9851caa490d42027c5269c45b06400,-0x4736cefc95ec8c516d487e1c57d69e2a261ca5e517c124cf7f3f100,-0xc4ed24c28ba89105f35c44caab3a02b1e5b39d524d76dbc5528a40,-0x1b7a266adf961110838b0b474d5c74c9d8df0189e164973146a740,-0x3267d5ad76b25a869fb3e92757a31a649ec5a0db3362fec33cc10,-0x4cee2522d1d0a15ed4975c6b76ac791b59762e840017f07c75d0,-0x628862bfaa3c1c73f8d0b33cdf1c1cac570452641d7a0ed22ec,-0x6a845fd6bf1bd0503bde26ae39b3f9e034db91f28adacb918c,-0x6182ff32fd59ec3018074e1b06792975577b66f7fd1ee259f,-0x4baf1f7076458dbfc51d0519f158b94d9f8133c05c527ce2,-0x31c27a375d1bbe7c41cbf74b4bdc62f6bbd1896a900f10a,-0x1ba0edad110c01209a449dae63f7c4dc2a59a0b58b7049,-0xce295cf18b51c15e4d19e6d9e4843876810013748f51,-0x50161c79f58e7b37a4e8f61cedfb153b9d41e58b0d8,-0x199a159480b64f950aea19daefa2ea71e7b38c6fc8,-0x69e8beacbce87ec40fe31811eb59d87836afcfea,-0x1598597415666d94cc1c551e03118d85ceab771,-0x357be65551a51a25444f2d0f55ad2ad24d31e,-0x5e82116293272c13ed57ad349222c853062,-0x6a278089d40a7d771eb2e24ed54c44f59,-0x38f784d6580e68eba7706c5e5fe852f]
def m25 : List ℤ := raw_ints% [0x0,-0x2372ce2abce19e8b25e1991aa108864e433b9a7064b017767d57617b91000,0x43dd932d7e569a957a7c50e1dd192fc1100032e5dbc0644b49e32acb244c00,-0x3f095b41eb898138ac9690b0be9ab684d6d822a39ad205598704433921e7800,0x25d84257f9ca152bc6b2998956d50afd8c73e4d832e10ab63de977b1dd498800,-0x1081bd8c783998c94e09eef34ea50aa6d01dc3673ce9b22986150c6aa07ac8200,0x5930771f4e70fe67913a2a37ac0b2b3c6e4150d4fd91ce1bc18c2c60c7c18f2c0,-0x184472fb41540fd9147f2a26d200546e1aa9f39401c3a856d35436877c84a4e0c0,0x57766450faf86a2ec75864ea649fcd7db3fae8edca5602d394989ad4fd82a5d220,-0x10a1df23d5322fa88f7fa3ba11f09715a5266043b3e242339e5aa478942a9a22420,0x2b59c01e39ea8629fe16e1f31416d541f4ac1772bd5208f667ed2c8c270d05dd3d0,-0x61e13e819449edc54fb14fa5e16054d2484fac7cdf51a284190e735a5fe98797950,0xc1211f325294d00b75dd703ef1a027b3d167a022b5094c1f2289c06410f29d631e8,-0x14f52b55dba20e56ab23f4ccb4e50ff609ebe31e1892e46eac380e9f1a6417fe9ca8,0x203238a43cec6a222543b948a2de2ea1cf68e119def5a1b4b9b6713d62f229c3c210,-0x2bf45b1f3cd3042d3b7e59c5a08c8c64bafc70eedf3396614b6ce2f3376fe5776810,0x35826128cee370924cac0b2e6b2b09f4e093e965a149242274edf8d4d1b6678602a4,-0x3a3db5cda84a5a789475cdd75d8d52d74b86b5c6c8e3ea7c5fd51d6fed5e7ef3f484,0x38c9c0c27c52a94d6d03474d0912b897080370ee0e9e2c0a3d6f70d9a65e2c528254,-0x31abe624cb4dd3aafa4d42f0ab013cc0e78ff06fde1bfb67cbb26fa77e74b06a1a74,0x2701a4da701aa19a0fa4759322ed3ebeeab0bc2d6ef11c53faf116cf3ed97d457036,-0x1b826ca33831fea1ee27dc4d6292a1c7707ea4198fb806da7707de7a40ff92b7b246,0x116bc8deb8108a3134d9f3f2f548d52dd8455f2e0a2713f3269c83786c84ad146d04,-0x9e66650b42e039ce8b6a3a809f1420088587128cbd212e00cfe1ebec719dbcf0384,0x50aff4027b81573a1fcc1317ea7dd89a34cb677ec27c2027f079ba2ba188358b9d1,-0x24c89c7f9e69b4eb24335c880f920450d774a7dfca885598978589fef8ee07567c9,0xef9d9e889678291b9d966bf1ffe247e83d1c9e502d22922f5c4d2f335687f22318,-0x56e5b867b2def0b5498b60e8cbf9a93d3574de8f45e3ad43e45eaf55400ded6be8,0x1bfb02d014dffed5bcc2bb24d54907284c3f9311ef7a55888ce060f798fc563edc,-0x7f8021e510bccaa02d03f55ab4205918dab01b031fd318074601b4ffc2e40d54c,0x1ff885c56afd521d3650d096b1eaec782f85a5e0edad08593b166e620c5313f08,-0x7053b89f195fdf4f62a882758772c3643c5eccf7cea74fdd57f3080e7ecb4118,0x1576ed918b76505ef90c67a0e439084970f9b1d0c3389d38e98b02af73dc3c63,-0x38b010a02efa169cb8a5ad6753f94f575373cb314d53dc8e419cd07752d653b,0x803336c45cb700df7d0c42ff6aa519e95ca1fb541482c186c843284d7953e4,-0xf5bcc8b8d8532f1061910d8dc261a0e3a2c24acc95b7a1696669cd01b9624,0x18a70752777c665849b26d00f019ebd1fcb975cad897e2b43a177a086fba6,-0x20a97533a0a4e6ac7c42fceb205b07f9d97c7b0715cc8798eaf384d00d56,0x231bb04eaf8c476b2a3cdcb769947507899d8cedab2396cb5d988186c54,-0x1dfc410d238d4a98aa68613aaf49e9f01e4af7d12a97e5b2cf7a127cf4,0x13d67f587b80073ea7a55cf9dbdad6d788262ac82ae6da764d0bd7f47,-0x9d9f3051bbccd92b613632bb951841f427fdceaa62621c727f6186f,0x3879afc20ce936895bbf2b5ca854992d2201bd87934b1c1ac52b60,-0xde0e9034be3570ca0dd52354e8645482999b433d9f8b7b347db0,0x2304e3035e5c617b911d65d0cc8a5ed208c2691f668fcaa92c0,-0x33cec51c7abde7a2743cdfb2c8ed44aeb3345f912ffe823d0,0x2783427c4ae1ee1017499ec1f4708a6813c58e37f7dd650,-0xcc10fcaebf3fba5881585a67773cac367a79adb55220,0x13c7966c71b05bbaed40512c79f9dec8b9eb36d661,-0x43fcdba5befed3f2784d4e20b2f2b24efe3289]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 25 90 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 90 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 59 indices rho q25 m25 25 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 59 indices rho q25 m25 25 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r26 : List ℤ := raw_ints% [0x25ce0d5d651c385d75926b6b79dff7189356b2bd4c0d94c158df000000,0x330eb9cf67d9f1d4fb33601acfe702c7a6bcb6e2b6333a990e9dc80000,0x20d41083cf748380d957e8dfb6aa4ca2808962e7c21a608f06892c8000,0xd5ff2ffe875b6431d44140401acf1f1f6600bd867b2dc364f5e9c3000,0x3e07ac5891c7ccb7ebf366aec99f97ca2f68dfcc1efd1e4c8942d6400,0xd9db17bcc54cc5970bd95da244ff56d52f8e19d874eb20f8e1186100,0x25a1fef791ab6951bf9ad1d57bdc09781933db16b83403809b362640,0x53f8096dec3e314dc843f258ab3a412b186e68f6513001530db46c0,0x99f29b3593ef42d3c61ddb71527e306c8216585951f64bb0bc9d90,0xeacffe208b0d67c88345ba702cf25290d937a2d25d720d140fef0,0x12c8c7a149afe9cd320d2a32fa7d48c637c913cc1538f3965434c,0x144aba3f1b2d328ed6ff77f56a107fcb4aa24542600a440f6644,0x128fe45fa265fa2e901558c224d69e319033ab382ec5c97a517,0xe652767d137d928a04f0b2ffa75ef07168127fd0320d3ca28,0x974b59cac831af49fb4a0127a0feaa5823f3f7d21af73fb8,0x53eca734b99230fda3112923316f9480124816b7b01f7d4,0x27196486f63a3d831f40a5d3109f72948d6c4d4a86a9b4,0xf2bf20200c5a09592d06fa37f0efdee2e978f1abc1e0,0x4d81c7b7daed552a7567186d6d8905a06bde4ee9920,0x1403517341d2223a4a2dd3c909ab8cb9b1bc7db3ac,0x41329e425e0828b197ab586f2dff1c9315a1c5a3,0xa138c52f60c50d466c2a908442c2e3ac4427c8,0x11c663c94da5ca140f00b81947f854be27594,0x13ed972408e8764c4599375cdac268183bc,0xaac1ae1be8b0fb427aeabeeb5632d20a]
def m26 : List ℤ := raw_ints% [0x0,0x491cc938259156fefe214bc6ec2195016aaaee87cfab30646284390edb1000,-0x8b287fc99e70053ee8e231510d43f27e310068fa153ccedb48648842fadcc00,0x807ac3ff66daef889dbac2cd234d448a55b866b89ab08ead16eb7cdc610de000,-0x4ca7b927cbb94c8ee1c5bebfbb656986974644ab0e746752b56dbfa7379dc9600,0x213853c78adb4a208b751c24f4c31df0e94f722adb3efb95469d28c4d3fbf79800,-0xb24d118dcce509c6044613419c502732948dda6931af248ca6f34c6e31b0f39640,0x302e06c6370e7ba2030dbc857bd386bb6d5d1269733e92f0ffee40bc16724b4e040,-0xac684e86e78d8dc5b36225d40d2933b5ee10992bba21aad2f84271c8752785fe6a0,0x208b22b425274fb38bb2028886f8ad8180703d22a1140c42ca77ef53fe2705cc44a0,-0x542bc4ad6279e6a29311cd956a1ccbfdcd6705c60e0662829766a09c7e1de828bdb0,0xbc8875ef5138dd92e82b84bf5a347cc8dd3472418f83090505c45a860863a4451830,-0x170eb9969014fa6d14788c69f62916a85d8c306749b12616950feca6f9a6b92d5ac88,0x27b0701c6a3ebb1b6dcb214110d63dfbcb80e5e8399d6fab44dc8d22469013464d848,-0x3c6d0b9ff307abc6bc1b1776ff32e78f0eb07026744ed2a411138a1853e8a9d542a70,0x51b948b274be74e730d1de2cb578677f617ae0a22c1608a976c0b7dd1f37aa1cf3170,-0x62851a5efc654483c1150402f64f44118183113af08d642fa2bbae9d4aba48a885344,0x6a244da6d8c843b936701b872fb7119a26eb795a479df9198de5d5ee5a2f341dd0e24,-0x6664f6745c6fe3b66a784fd9796dd3f886c01875a239fd88c014a05d3df13c94f984c,0x58912b3a08db04481bf4b01850590577d1f46cd12649d802ea892dc8dd541eb34f7ac,-0x44bdb88ad9bbc85e57addc3571be6c6261962e8729c4070816b120c6d85288d22025e,0x2fe3657490cd3c53ca93d2c2a2cd37531462b1c6bb4aa125d850ea4da36a49eacb2ae,-0x1df01145d3ac58f06597eb5bc44094f5da1d54f08d807f78f9386bd28ec5ae7895c3c,0x10c8a57c8a26cf81620ff5bc0d7f13a8efec6666c319b43f7c3bfa85dbb87a0531bfc,-0x86d9f813589423f1e1b27b246daf048bee19d4d3a296b02caa520e890a55b7ebe7d9,0x3c8e78d4cd8fab63efb8bf582dfc6f5cde9e806b89539156dfba13f6c8b5b1b73511,-0x1843f3c617e9e6a0a02f17df27554ef644a2c0a6ea081c12ada4009da424970d6330,0x8a7268a6541b4f29171cccc7b85668523713fd08408063f86d83a07ef515c0b7c40,-0x2bca46efbb42a470102431f5a70a3a16a991b2df8a045fb06f625834ec86091e724,0xc3cab98d81217d39aef6342ff1bfff72e8e42664e0779eb33e70ebb8dc88789ad4,-0x301d1b6c5aff55ce7b841707b1188b0dbb9433c091f40092e15cf000017f4d5ae0,0xa5717865a59104f4c535c646e43e47bf2723d2d0a267e9c77bc3b49a3c7ed0f30,-0x1ee52f1f05360fb5fca7c139157d64d875e27e425971e45c01429f27e9713348b,0x4f9b514e902a416ee2a059e02c9dcebc23064248a25a5a459195a5b652e647a3,-0xaf535d2f61777d50f3602eb6ccb308be8a7e701b85fc8c040cd80868131e3cc,0x1469e2fe10c1db9ed6396a41e4f23774113dec7ea7e1b6bb29f3686760f9fcc,-0x1fc5bc0f722e241357d1bbc54bfa4d899da8cc76cf02359c2dac4c8f768a9e,0x28b6be8d4b0f291969585bf0bcffb4829f481c7b723c68f0479f9254ad70e,-0x2a3499318b568455a2c4e14ee48ea20e7b93d0cbcd85eba016497e81f77c,0x22a6c4e8a6b632b305b580952eeaccf4e892e2b3e2285d8aa30341c73dc,-0x15f4e83a5855a3e37f91180a2ecdc8b306cd7cc93064a45e91906a725f,0xa665a9c8a92c1a4f827a869788d9016e2e9fc90f04c05b0970a46547,-0x389955b13d636e4b5ca8bf1b06a99fdff3c3573360dfc68173aa188,0xd22657e928c13597214d8d1ddb0cb0aa3d6c5d2fae45b0aec7598,-0x1f1bcf54cb538a35233e1cbd373c81afcb30c5abe84b89c686b8,0x2ae8a27bf487d3c8f2ab40ebaf6905a52e35107cef4ae6d888,-0x1e47a4bd7b40a018ba53e0acf72bc3912cfe2b99c8506e38,0x8f7399aec28710244250bff65b636c06030114520b5c8,-0xca0e1a2eb4fade3c237e78038dd621df8c707a11f9,0x26f28c3ea3ef0a57e17c26dfd17110b69f565e1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 25 92 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 92 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 59 indices rho q26 m26 26 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 59 indices rho q26 m26 26 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r27 : List ℤ := raw_ints% [-0x7151af2a583663171839b1e17451428163270ba8430b1a81f032a000000,-0x98fdb08dc1123e3a10a7a9811294555b7a98a25e1932c9363ccea300000,-0x6255165d9ee6c34cca5415b74d61e225684a36488c401331e27d2bb0000,-0x280be8d94487613e0a5da204201a966019c2d5f411cba5bb211a3aaa000,-0xb9a6ba9ec25f0ac226edb620ace2abb460bd13a67043f65e0a6ea98800,-0x28bbc9bc6f53f321a0e4a07a5d8278c431387ac8d24ab67a29ae338a00,-0x7087543aa7cee3c0688ff543e4f8bbb86c9ae9395b10d9ad06b8d9e80,-0xfaf44178e96af1249c5fb6f208268b3812d953ac99b581d01959cfc0,-0x1cbd8ca323ea59400cfd39ef655d2e4c81fa543f8ea31e64128ea320,-0x2bcfc3e99ed81375fef6f7481af68308cc5b31be9cc733dc42cd470,-0x380ab84ad855e93efeeb4859810d5061dc433c705c3ce48bee6978,-0x3c7fda5d9e445a9c4801d3fbaaee5b55ae8204cd5066909ec86d4,-0x374d718cf9f444243e0ffa603108efd2a133ec5913ffe53b2bbe,-0x2adade34f685d3dad00eeb808e75565c5e76031a31090f55603,-0x1c20a06edc8af1b2ac0b051f12913aaab57cbd5d9476e6ab14,-0xf96b80b097377d3625beb29a4d9cc4ca265cfe315dff835c,-0x74171d712eb4e6f81b6fbbf18c64b8e340b6467106c63ea,-0x2d00096de8b36387f1c4758a9544c9eef9343101a8f082,-0xe5a2887fcf5a1200bc7f7521e772482c5c97825f9970,-0x3b38e6326b24a877af8d244aa139243acb6eba0f2d8,-0xc0ae3c34e736c10f504003260cee975ea093f4672,-0x1dbc928ee6ddaab9bc26c387ae90e8bb7ae30943,-0x345ff853562cee8928e00aaca8e19e543f5784,-0x3a9ea8ee1208b4db51e382453c38f6efc500,-0x1f55bfceadab8e82fc7ff3baf39fb73ac6]
def m27 : List ℤ := raw_ints% [0x0,-0x96cb5f03cd7bc36dec24ac4a47054352ec008bf81c5113cf0b30b5aea3d1000,0x11d6288076a81d7a6f8d61ab595dc24244510d883cbcd6aa4454f590a25674c00,-0x105f083f6f6f56a67cbd8bb560feec2cc8057e876a314f7539923ead035bb67800,0x9b556903d03466c2f8298412ad446484c93ef24b9599884b0cd25c7b5b2e4f0800,-0x42e4ec0147a5524af2b763e0800e052ac5324bfd264f4da1f542c9a6ccef6c1d200,0x164b48f83369a0ff0ac6d999e399af9a3d564595196a984c2dadf09c95171ccc7ec0,-0x5fbcf23631cc8f0e3186412b87a3b59f3cfa8de985220e7196551db42c8df48aecc0,0x154328bac8568bcb3e4f159c1ad813f188d9f890c2f12cf37f71312bc909f37bf3d20,-0x3fbff84a4d71c0d8684bd192d3b16192843680acbd69204e587d4a4ce241e95118720,0xa3a47002f841e509289474273cdac8005eb0e0c3a481fdced89834d24416c463251d0,-0x16babfe8b3bb94529b73d963813461b0db923522e19433111e5ef1eb9d17f7a9435750,0x2c1d70f62ee44cb88a76fa35187d03f11259d8433507b60e59f7c824e7e05302fdefa8,-0x4b4ae21004b884b55f8f056dd7658dc64def99947353be6fd957f34fe3914531bfa468,0x719e9a771cd6d6bdb80446f0355b2598f948e4962f943ecc8a06d5a616cad0298bb690,-0x9840744f8e933e0eee284136dc29903cfb0fa6d55fd54bba7e06a1d5a26e1ad8b38c90,0xb5c7a40f2d309fd53bd6b8522834958c52a841f94ac6af6dbcddf17c50e2395ec979e4,-0xc1e08cbf11ff6601f9451816b925e960d4d13a02a679fb2c3723507e50741bed47b5c4,0xb911822373853f11a687ac8bb052f540db6ab1f40976fc17bf0cead776bccb6439e254,-0x9e511b7a4784156f3e3d3262bdaa7500d4d2eb2c773b4aa068ae53564bc074988dd274,0x7975fdde4e17034ba1e085a0eb03f44650ec3b8df64f7ce3a6f4494b2656fb64d12926,-0x5397788066a204ecdc989e6f729bd124622707fe27557a350f7b0328af1aea89d4b9b6,0x3397f83b354e8fe81fd633721a6f2a1ce52e1b04d559825ab6665f58a06dceee4d31a4,-0x1c899acdf272c06c43a8dcbda1124cdd7ebbbd6d5866b188a7f7c967030026eb3b8424,0xe20e26bf84ec7ede3076b55aa17e88a424c117fd0029b9e0123cca5d256ef9c911661,-0x64007b5a76d64f884a25eea749c83411716a613680aaf05327740a3b519f4257048d9,0x2770eaca59d0b0a274792c056d61434cfa5b4acc5a9ceb6a71a64db8164ab41f9ee58,-0xdd48911ecaedc72657fdb7018b06227283af33a8d02a42cd936eda1da6bdb396eb28,0x44c12133400ef570c1cb561d916ced78797e08a7ee96951983a7e1987988b625b24c,-0x12da3af9dc4af3434509cfa5c1c45303876bef027035ebabb25e61be12ccb11aa53c,0x48a4999928409bd24096018a53e5a1d624c959d73cba9a1b2662025432549788e68,-0xf4767de999a0ac1f84bee3050b323c53a5e0e48f5de56b86cfc5488e63c59c8078,0x2c9c5cfb815c9c38a1376fab7ba813559c887bf36e4cb479832bf11894a77d8bf3,-0x7023988500b86911307cf7fa8fa7bf9b2a3f6dca6521b96cf0ccef52e631dcf4b,0xf07e9edf565a434c75cbe818f13d666d72ba911659906d35f341caa69f2d3564,-0x1b35d94680e866fe6d204d2035ec039ba7da679cf4ddc152ea03a4f947e377a4,0x290f3c7f373dd06cb273bc7f703b586684385d0a42fdbaa1b523874874865f6,-0x32e0c4c3505bec577837ffbb37646e04b51ba77ed27439bf7dee53fe789326,0x32da5b0f151bcb0b080cdda2a6288cc67c7b4d4e9cd6fae403f769d6d23b4,-0x281fc22d1cf62f5b845d3121c56609fcd42733319a4c9c42a2f441fd1054,0x1857e82249596a8f2181f89288b430bab697654890d454931c9b1eddf77,-0xafe7e4af23cd6d6ad9e723d1ef07507fb38a7754c62ab46579ee2ee1f,0x38c8786e090f6d3c06167c3275b4d7cb31f8d73092cf10b577021ca0,-0xc706cc784b2932082cdfaf93b141f96daf6a03a4cbc3b2bbc6c2f0,0x1ba57f9b455ecce85562387b98345608d2b28430135767158c650,-0x238b35fd235669cb586e9d1f26c8cb75575d3887126a48416e0,0x17340984ef75d08ffee85fd79ab5769525e1a052c9f940e70,-0x64d2fe6d2aa7ea0c39d574e8054decfb2dfb89633f9240,0x80fa053d0dfe91ebfbde464b694fbd0710fde79dfd1,-0x164ec887c68bce97e5a2645356772b3b806f4579]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 25 94 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 94 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 59 indices rho q27 m27 27 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 59 indices rho q27 m27 27 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [-0x1f55bfceadab8e82fc7ff3baf39fb73ac6,0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r28 : List ℤ := raw_ints% [0x14cb780407a0986e487823b24e2116b552828ec0d7397bbb5c4faa6000000,0x1c10d7d007f5700ade895691d38024cd866fcbebd4d59dbbcf73d52500000,0x120858e48041a69b0206342adc7c311d2557181d8f7d2106a5b6b15250000,0x757592fb88a00be5162991e345fd89834fe712e8a768e80c2b3e5f0ee000,0x22050ab8ff42e3d97121b98133839355576a7b1b56495e1af65ae9a36800,0x7760b1648737c318d3ee826925e6ab36ed5e61dd89dc0b62ec4a5767a00,0x149a3f0d76290097e539a602a71558c324c3ec4f6a1dc610824eec9d280,0x2decb08074605d21201c9ecec534156556311c01cbdd34b21e9b659b80,0x541bf1223eb821c8986dc15fff43623292fe4098b61e6e8ffd61ced60,0x80253afe2e10702979fe367204f879e8be731ea8f61ac5033251fae0,0xa3d2ab6c4897312a435c3a062178be54933d28ffcf06b79671b4868,0xb0be572f16f4b44cde5aec4b1621a18a71a1207015a81e2f3dc568,0xa1742b0142287c45949b0d073fd912fe095865a851d26957029ba,0x7d063e2cd682510d5f150fb3c2b6f6200b1153636fd963e00278,0x51feef67f62d8b37d4f66ada592f7ab57efa5ac910ca5dc09a1,0x2d680146c835ccd5824c5d88ccead7c9ba9547823abace6378,0x151d82d0853c26ac9627089d5e02a809da0dd8c4b77a57c56,0x82d5912705bfff5f5e9e22179e649a8b69f89ecab3aa710,0x29af5ad9589ca70f412293cc5238558963cd93a44832ae,0xabd10906ec1b3eed7e6103ede9484d585c8d846b7058,0x22e5651c965dea441add1be3b9591a248397b89597a,0x560e80c407afe4a5e8a6a2c00269167cffd4e9158,0x975b46cdf8f981239212c5e3b2ec95c450bb0d1,0xa9246e515ce4bd493ddf5ad8a77debcff5b88,0x5a4316cc8201e674deee491296593d3c30e]
def m28 : List ℤ := raw_ints% [0x0,0x1370373f7d7cf4312b70ba359327adadb06c120afba6738db071476b831df1000,-0x24959397e73216672d240c1135a160a8ace72be8fd457abf2cef3a7a4ed250cc00,0x2162f29edcf5915b9de4c558e1875264d34d3bf5eda2c5328b5f8a34c2f172be000,-0x13ae6bcd1c891a00c55ea0f87aa816442db3edb19fbf23b4bd23e1d06ed79b469600,0x86c794fcde74372c56a7474591871e2568209e23a96937deb36f0cc53e184b502800,-0x2ca2009f436e9214ad2a34886fbf7fe457efa283975a232afe243c8a33f91b20ed240,0xbe6760226a979109986ad4174a261e8a5deb1dc3b5f7ce586d8894967e13087eb5c40,-0x29ff4248e8f0338323f3515120cabc096084f061d3e383f30685fd0b6edb24ff3215a0,0x7d05df9a7ab1a4366ce852f90f789347b1783846d56c2a93be4bb343547d0929ddcba0,-0x13e8e579d2c2978b52c02a35d63aa3ef8604b0fde60786f7e6f0c6eb150105cb9d24fb0,0x2be8181ff2d4991440f4321c08bc7431ac65bfc0b44d124f53171fb0b799b4f8abd2a30,-0x548913ce9ac08e844e0f3167b01afd171295baa49084cd4794673211c6a372acc9c2f48,0x8f13ba97c2b01fb69379550f1bcbf0cc521cd08f2232f7b70547824435afcbc1946dd08,-0xd60871b3f709f3443a1dc73bbf85ae2d469e5dcb48b7890334a3d768bbe770a27d4ddf0,0x11c34a826609a5c415b5917f05c7ec466bab88b1fa2b91ae6cdb961ccdc6edc37899acf0,-0x1501c08253a29baec4487852baf2d7352c29229373989e6754a7e1c68d3b34156fd13a84,0x162ec9fa4fd55f5a113afe7216d84176dcae2d20d6bbfff996e0ab58899668a9f8a2bf64,-0x14f4861c5be7df5360b273d029ccc917cc2fac0f9fa89602184b35423e5bba5d87410c4c,0x11bb2bcc834a82e86ae812d83e032bf7c7b04d203c43721f902bb8701fb6219125b5a3ac,-0xd72b65b94f05e2d24246e867711361a9ef57876e60f531022c250aaa84541627585338e,0x924ed7acb7fefa466108410f701e2965bb8428e57561b3c72cdd0dab750a1334e22b85e,-0x5929e0f9ad86614cda73ba92699b72540d42f496e67ab238b75bfbc03d275f03b9fdb9c,0x30a9b1076be79ab3b3e9fcd1eb3c4bdf62da516e74f3092415c8aa222d2284b115f055c,-0x17c12286362a4c46effad2d378b7a6ff67a96ea58a0d5a406a85293bddbc7a5dbe3b269,0xa5a5109e9add7328a452882ccb1db0d0bf4cada2dd69ff780783797194c3eecf6cb421,-0x404e9695c2553b6542fa3f7af337b8bcc24580638adfd300cbe0d5796232eee1cd50f0,0x162cccc5ff3f35cd658c59012ae34a0e08c397efe3ef3b44929293da35fd0e3408ba00,-0x6c4b73db8e779b0e7e9fd366e5e20a851011a1a2c5ff428e5b94d15abdd8569230454,0x1d2329d7bfb031e2d66aed0d108a030957a001b84569baf25b3a5803f2cd8fbe37684,-0x6e0746d429649cca58b7724f450c6a8e0fd968e8fd906aa8dc489b1b0365625c4a80,0x16a5e98ad99ecb091536e7f64e4bfa0c8a933e09a91ebd0e3e21e1558f47784d60d0,-0x409dbd8abbc618b907d3e57acde0da6de561261836dff44fcf3d71369661d079e9b,0x9e726bb0bc60c00b85f61a1a4fde9179abaf338b4eb84ae1ec821a6b61b7215033,-0x14adb40925f5358b1b5562ff4b301dfd7586587fcb19ce09fecb7a3422dd82804c,0x245f285e42eb68aee170c1f38272486ecf62e0fa1464db7d0c96821b663c9e44c,-0x35337a3e53f61b1f2a119f84e300a8126d3227b3b764f512ba1653dbad9b5cae,0x3fbbfef110eb2bec5c26c7409fd11aaeb73bcc8ebeac2f353489e74a1c82e9e,-0x3d682f019b23313da2d0929a721d3ebf23e33e765b8f112b5943277cd1ea1c,0x2e8cff97c4391fb28b11ab89b3ba468f23efaa671ac18442d5bbc2c54147c,-0x1b08a5105f1975ed61f3d7ab5f9ee461c85e15bdc23da9d96b75e5a3e38f,0xba343e6eb4c15b0d1bb5d1995ba149fd7116af2bdc27c846f8547e53f7,-0x390652e299a5273847642fe4bc4447f86fe62a011025609d7aa434548,0xbc9eb33231d2817ab6407c6ce82bfadc76077716d60b38980376958,-0x189438ff9182c63d2c7aac7d05dfc4194cbcc36133382a794c3388,0x1d725df93de60e8752d8f220feef55f6deaf8a95b60cfead3ad8,-0x11c78875c61a81a13ca4e40b0d6623c1e0a34bfb66042de918,0x46d9f9d999faa9ff768682a513ef20f4b721dc4f4a8aea8,-0x524fe320985546c5b8fd3a2e29369d196991c22405e9,0xcc6681d593e4067c002729ddff417f33e9aa8751]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 25 96 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 96 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 59 indices rho q28 m28 28 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 59 indices rho q28 m28 28 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [0x5a4316cc8201e674deee491296593d3c30e,-0x1f55bfceadab8e82fc7ff3baf39fb73ac6,0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r29 : List ℤ := raw_ints% [-0x3be68b4cd7f67920aeebae38e42ce5474c21eb3b77832f95d791b16e000000,-0x50d20a2d0bd4326c4a19604a557d860d50a78324e97cecce3f83c5b2100000,-0x33e949afff0bcd6edf7f9814fad06983fd5b0a1b28f763e51f32b56d810000,-0x15204bd924b94d8a09b93bc943f7b62f712da905ad7e7df963252efe4b6000,-0x61dd395f7ae49065110c7674eaa1356356f6302737795cc6c351b1e1b8800,-0x157472bd600a544a3adcb383639115fa6acccd9b72f8736764444b149b200,-0x3b3813802dab5812e6330aa04943cd766223f4da39205147f9da85107880,-0x83f1dc81ef215523d9957dab8d7c1f7b3c0fb1d320ff8dc99d3d0c91f80,-0xf1897201b06faa485f3c9bc1241f705204c0dcacde377215d1ede34f20,-0x16fcf2667c4ed6cced70fa99b3e16d41c207a2f3a7b05e5f833c0e18a0,-0x1d5f509858c3197fe79c1a092e5a7bd57e80fedbf3094630c21c9f818,-0x1faba69902a32a853999f95e645c89b502e0e51e4aab69fa085fc8f8,-0x1ce9ad956d1e20c7d5f63ed7748b43b362a5e84f743989823a78cce,-0x165fcdd6aabd9bc4192e3d9237bd4dd2aa1b80879f7f642b2b4e04,-0xea9d7c574bd9a928f6f4ce2ac132f6b6fa6c5bf6ba55f63e02dc,-0x81d273221a9857d585963ee1ce17e4b9d21fdd1e1714be3c17b,-0x3c5259e05af08712ca862b55a5ddd932f5005c77f87503dd92,-0x1756f6cb65aa1bc78224c3b371e3895261c58d0159c2dab5c,-0x76ddf47bc3c7962ce2b09adc1fdf65aa5896c10efc6da60,-0x1e971776c6ce8c55069560ed76a76bfee863e31073e07a,-0x634be6d95df52765a47dc5326aad8b84322dd6c1c4d2,-0xf494ae92f9dc3bf3fb070c3c9debeb238689d77cc8,-0x1ad9c8960d8d8eb6424982e7069937b3d697ee3ac,-0x1df6b24484c7d4107fa9224275bd5a3052eb4cb,-0xff7277009b928546f4f510276d716c47a82e]
def m29 : List ℤ := raw_ints% [0x0,-0x281771f2f2d1b7a56998800e7f81d6363bdee536a7074e543be9a34dbe6dc11000,0x4b0c408731c6016a1b3b3e23193cd75be49cca908a5f4d2a4cad689c4291c6a4c00,-0x441afe6f67796414dec07b2eaa9c13cc59e6fb3895300844bc6ec05dab5a4cce7800,0x27ea727e5d8f854ced9dc9f668e1afc81d4ba0307e70d0331406984f95d88c3d48800,-0x10fb537c0ebe83302b87ee4a89119253afa0216d1aa07a23adca75974d4a12f439a200,0x596ae2c813ecde1493b8b6507082b4d005dc45acab070e498a702e6f48fb2e2419eac0,-0x17afe3bf9c3f516612316db5530e278a6eafd14c2b47b116532aeb335ca35a9030cd8c0,0x5308957333187bfe3cf5ace76b44af883794991d008d6c36443ed1ea8de2cd6aed9c020,-0xf576a8996499f46fa527ad84c9cab8658a418f21001a04d4ca7e6cebd7847c24e824220,0x26ce7247e838a46b1f5ebef374a9ccb8848c929e15bb6cf0ad227662941552928fa49fd0,-0x54eef2a1ff0f4b2b51e5ae1ffb05e8e1217b112b9d1591bf4eab8f88cb8241dda27d0550,0xa23d9ba159d9ec5c646b2aa7507d4e31c84d3e4a32710a7803eccb7c3e7eaca708d52368,-0x11057bfff53bc3b5dcc09eeca32410fbb2f73c3275a3393923f1131fabd743e5e08723228,0x193eb54dec331b44e93dda3bbaead6221afef45cb8e612f83fc33647ee8010aa89586a710,-0x2138db309fcdd1b45513f4f8923a384c581c3159e2a99d38556f258ee7993590ed1ffed10,0x26ec0dd51f97e0bae511be3a1f1ca07c856f2780febf9c4683b791438bd027ecae7738124,-0x28b2db9ec0fc776627b032286069452d3a6347d60434b849358d02b224a85bfa7e40be704,0x260d5707077f3886f62b2214275ef6d9add39a72fe023cf2012c2a5fa50a9e0f440832254,-0x1fd9e91365f0527f01a3d8468a9494536854f9ef52885d81488d6b5304ca86ac063464a74,0x17e2666fd4af501c8dd8f623da17d99c2b62181a3c9982e379f757ccb184c283297c47196,-0x100c2acc4f35914b1ad9206c09d5d5576ca9a8ab7e2ae498434499b085295a49fd04524a6,0x9a8473028b7d626722ff9e4743bdecb9080dc506562a5346fb34c13021da822ea458a144,-0x5337cad39fdf5514d5c429d8a1ef7287946d9af2ba9f3d40c9d94e09b27f06edbdcdbfc4,0x280e5939b4b14e5cc09d91e21f56b206088831480c162e52b9956fdd6cf1c7fe65d772f1,-0x11333b7fd3be7229a3e2a37a0bdcef2ef36d661979bf97f6d6ef64bff3ac5a8a7de021e9,0x692bdaa22cc0695468f86695992b100e65ec1f8b3fb18e9a8b3bc0d05e526c606974998,-0x23aa5a3256b32b7743e4fa698d1879d107a824b4bea020a7d1474bedb504ffcf83c5268,0xab1c3d783bc279d10f1b1650aa2917a529ececdd1479f37405e958ca79c699cadd343c,-0x2d2cd5a3a9dd35343893d82a359d9d0d190d27cff0949333dc1f9fe3a30656ee48d7ac,0xa72daa0d3b701f98d955ced78594ae72f9fcce497f3cb0967b9e93b398a140465fcc8,-0x21ad13d8e29b7cb43a76ebcd95007afaf7a589f6adc963ebb577f32909249d75596d8,0x5de122f125b3a1e0a0a7edb0b27809483a8191c5d9d2c686fc0c2e8f920c4ae1bc83,-0xe08ba51e39f3f31a98689a9f5206303a0ad2000eda09bfea0afa86642b440ed925b,0x1c87a7eea169ec34895225be22dfd27bc26d5c24c047d3d3d5a758db8c0f5d6dee4,-0x30c0251496463775d7f6007ac9260b8bfe1b11e7d0f78b42abfb2a4a1aa6247124,0x451c196206db30bfe9318d6332dee5204222650b50f4da735ce4c646c95aa64c6,-0x5007220877b77e5765341dda0eb734a0e7c83dbe7f55bf10699e055270ade976,0x4a4f149828308190acf2c33ce099798a8c5c35380e116675dd23c3851fa9414,-0x361b73b8c96f10a083585c2963df5ae12313e2e22a47254ffe493ce94d5cb4,0x1e1189f1343baa88684d09142ca1a2ccbdaeb9cf112ae56219f4aae4ed5a7,-0xc55a4f91f513a8b47b2f2954709376f782f9dd92c46bb01272911cd21cf,0x395231f9eb675efcfeeef45fb11d24b331022e7094fff661a79d41e5e0,-0xb2dea3b568db8f50c48f4b2777880c7eee26555149440cc73562d830,0x15dbff27834328edc4e28ad8cf9c31c062f68e3f2357e1227fcc160,-0x1865e9764310f5d1077bdb5919104d9e48af332d938024d03dd70,0xd9f577c5e9686770a649f48ac6fa9506abeedae47dde620790,-0x31c7bc96d308ebc331c3bfafc2e4280965954af4382b0b60,0x34853b09a2e2d5feff36b1b1e03b04be743a417ba5a41,-0x750926e8b2f92dc291ca4da848f79ea7f772c7169]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 25 98 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 98 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 59 indices rho q29 m29 29 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 59 indices rho q29 m29 29 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [-0xff7277009b928546f4f510276d716c47a82e,0x5a4316cc8201e674deee491296593d3c30e,-0x1f55bfceadab8e82fc7ff3baf39fb73ac6,0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r30 : List ℤ := raw_ints% [0xa985b0dcf701917d0fb7258004dbd37086f33146ea2d8c0e041ff908e000000,0xe4a944afebfbe0cbd72bd165a07647202ffecd49bc8ba88b0180f6739100000,0x92d335d3d809688221e0418f64610e6e74c9f1c32fdec6255b6e8d5fdb10000,0x3bbbc2a02a1a8209d6d5f46c94d5f3b28787d28b1e377837e17e3ad81c96000,0x1149c84d9c37d06fe682ce69af067b073533dce1c2d920583893dbb84008800,0x3c9e94867b9b9f7ef82ccc5b7f992756e8bca98ee9b3ca0dd58c2e0c71f200,0xa74106b88b119fecb01b2e1c3141a5d160804160fc30aab5a8af6a5e69880,0x1747fc26334d94514401a213e1016c8edb9fdd58f1e684cfd8886cf3d5980,0x2a996b00fa28f60f06df15ed6e6224784f0cbc2ff1a5d80071e328ed4120,0x40d6b5e50ed91811791018207590f91ec905ac051fefafa113746c556e0,0x52cdb85dacb355bbdea5c74684956ebb9f452a4de52453cef5f562c2d8,0x593be3f0a58d573900f027bc3c769f61c9179ea2e0beca31b6b8fe348,0x516aaa68b32c63fe0b234357aab348a56247c161ef3e7ea60fd203de,0x3ef723a21ee0b45653404840c953c7d4d95621f0a8ad481edb07510,0x293d0657737b80da10db4fbbc0acc0de4254d630dc643fd5f9e610,0x16cd7a5468e7424a3c6ace4aed1d5a806b1a06349512bb9f64280,0xa964fb2a1a11ae515594a20d9165e7f569590bcf50fa72710ef,0x417d158c5a5dd61a35ce26c103c01d0f5102636bbf5fb47900,0x14d3c05fe0a6da94790e3a302a5bba2059cf88d3ccf616f14,0x55ad178a4f5fa59809187c237c57d07e6e0037f61198e48,0x115d2b802d699d6a6430f0582ef51be80999d003b24410,0x2ab9010877799c75e6afb009346bb6d7d5d27a73a750,0x4af43426b2601ee69bdfca4118ade2369a4eb91bfc,0x538925110dab5ffaaf87032cea54776860a6d430,0x2c7299c3f28e3a4a89c86df97f9bf809c5318b]
def m30 : List ℤ := raw_ints% [0x0,0x52b05b0514d08ac529ca881de6fbc9cfdb7bb8c0b87f118dbb91e0d058c25e31000,-0x99f8c552a085c955746bfaa7994d7c2d878361ca1d648f273e25a7c2494ca9b3cc00,0x8af77e07acce5449c65a6a46636784f07f3a4a469422af0df6c8382dd66659b49e000,-0x50fc94e802c0a520a6d267bee1ad2c90597abfc2f4a4db96807e588b62609b76109600,0x2240c28f546b36cc7dbb7a4be4a038fcf2bd11dde7e3314fbe4968f135f54c99db13800,-0xb3432614ad86f7814191096b28c09ce04522f274cb17f69aeb095643ad30e700f006e40,0x2f2ff3b49fa8c5d3dbd049fb598d2a86d581f70db3d814d7375423a13cb7c451598c3840,-0xa453710e6d04bb5353d0b8b90ffdca625a541677e5ae38b2d6a4e37b14b1bca167f77ca0,0x1e2763013321e42b81f462bbd5a3c8cacf92a88d38ed60f342122d6b30ebca7b0c9a9caa0,-0x4bbb6d7f1d9b40b9801e2705cafb1a5eb67e0c4450b401d92996e62d92af53e6dae5bd1b0,0xa485c25c1fa137069c0785a09b1d09ee72d469582cab7fb6180aaa1ed5a7ac02d0b8c2c30,-0x137d832cc9f3fe4cafb62aa5a9537f91b4fc862703a98d7114a2e134f4404c71963503d008,0x207407886b5cdbe2a1f482ba9eba9d10df65bfc03ada2b895112d78f1a80ff25db0ae1cfc8,-0x2fba12c0f6f6a8bdfda8e0df3931d4e77564d094ded72c0d12e9d20dfa333d6b9211c17570,0x3e41380a3bacf18277139542feefd3f5062a684e10add1d992d0113b96b2517609238c8c70,-0x484370a60aede8733858801ccce85c38dca3baeefb3c682eee5eabd50e7b17f053f32b01c4,0x4ad4f0fa859e2a50a87e9105fb758278c4f61bade4276ea92e31c6218446ea3fd8d363b0a4,-0x4541abd5ffccb4fa4e13535210021998fb5b040b4c755ab0cc38f3852b6f590f1d3554904c,0x395a852a666bc994b5ce5763ee8bcbe6149918a2ecb33ec6380d45758af58459336d4fbfac,-0x2a86d01c0f9395e8d52e7a24596c634406c9cd7938d77f89ae0b04c819ef837b0c7feb263e,0x1c3c7e6090b75a1ced04c27e9c9232b4765d669a170c3cca770fcc8a39f1104f050f59038e,-0x10c80ce135029d383f76e94f0411af4152b37225651726bb13c982eb33fed8685787be87fc,0x8eb6078d3529d68f0969a20a4a28653f9da7b6af5f358be9e5d9e1360a08d03c53157bbbc,-0x43bd8b25e0381942e7d8675b258b3d6ddbd8b81dbaae28cbec935614df4f7035415e830f9,0x1ca939eafe0e3cab6356c714874c85f9cfda8d090b26e806aa112dca7377500b96f33ff31,-0xac85f4316a0ee031afbbed29199d0c7c819b0632bff711c1e5b99c5ad42622d55ad57ab0,0x3989f54ceca2e17eeb0b948d415c40a306b73cad94ce41cdc31cfeb53b329ca9a05babc0,-0x10f32c2e6697ac9a7d760033db5981288dc05b850a5808f69ae804e25d07e05ac8412604,0x4642029ab560217caa83f9f6381db3dc07fd81d21c42f3c3aa15e5e84878d5586e8fab4,-0xfecc7041eac0159db659924aa389ed0420348ca1de690130037a50da9ff68f83b17f20,0x323a2bf2dc429f943d3019959b66956219fe3b8667182373f04bb278645dff7afe9f70,-0x88ce2a75fb157a0de5fedaa8e390a27183e4f2269d2411d2cd947e79d01556916c9ab,0x13f25e2de96b6ac3002928d502250d22d5aba6259aa81ea3027411dc99f14243591c3,-0x27791624a6239c7abdd7870eeb281c41c6e7cabe555a147ef75440015ad546dd9ccc,0x4184511e75aa0b34a8cabbb5dc451af6cff4e007766e91171f0287970aa293c38cc,-0x59ffe53dfa9c64f751c3a0bd2da13f67a2ddd3e46d7cfbec7bec84f1846086213e,0x64b77ee5b25b2423f605b4989fe3ad990e54de9ff40cb98c394e787c1c80404ae,-0x5a1b2b124e95dfc319626e81f861d780ed89f14a02f786cd863325fef0dbe3bc,0x3f00ac61b98df69a974b503da611cc3331b393cf6a0b25bc7651c2466382c1c,-0x217e746e3280d72465da65ed35f9b2462dad2723fa02320150cea595734ebf,0xd16b035f1d152d9cc35f607e6cd5a6f8501ddd222b913fbb267345f3a4a7,-0x39ab72a03f22219ab010a99ac19b749381e0efd25810729bccebe6e4d08,0xa9b8d0028704d89ffa5dc0ca4fe670f84f88880998e0ced749876d918,-0x13725730d69f5bcd3567eb5922d2ab541ec59e1d4938655bfc7f39d8,0x1437788c0a623ef8e94592c8c852fe06771decb4c171e76389f2a8,-0xa6fbf095f0ed9d234253dbe3aeb0ab1af36057e2337670d86f8,0x22f82a466b08052b72a1e5b16ddbb5ee9dd2963c264c51288,-0x2181399c46e2535496a3552421ee45f133bc00c18442d9,0x43007d7597072a5f2ecba5ff93100a199b81ae59c1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 25 100 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 100 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 59 indices rho q30 m30 30 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 59 indices rho q30 m30 30 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<24 at hj;omega) moment_ok_30
def q31 : List ℤ := raw_ints% [0x2c7299c3f28e3a4a89c86df97f9bf809c5318b,-0xff7277009b928546f4f510276d716c47a82e,0x5a4316cc8201e674deee491296593d3c30e,-0x1f55bfceadab8e82fc7ff3baf39fb73ac6,0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r31 : List ℤ := raw_ints% [-0x1d7f2c95f0877207d5971a069606b8ae1312df31b9032b28ebc28f895fb000000,-0x27c6b151c4e2a5d2978f53f688b8e9e1a4713fbf5889b4ba259a7622974e80000,-0x19887efb0ef99653f2c5a415f8713b848657bc0da23c64c68522bdf8fd2a68000,-0xa62740c7e39fa5eb32b472116491967e4a31ddc78e0390ebfa005e039e507000,-0x3012a504439dbc777edfa68c8b7b8bbe93819c837e3270256620b00617048400,-0xa8810de67165ddbc1a80c1d0fa110ee21f39b93989cbb2f52a3d6b1bfd73100,-0x1d0be9181295e722b76a29f55334e672a4245b250182a4c2c7854e856edba40,-0x40aa5374346f86e43318da95c4f486dffc09e8f7073c3183795f34ad86dc80,-0x7645ee6181a0239ce9f5f554369189bdd0e305684be2b0138735e5a43ec90,-0xb3f03aecc5117deebb2613d6d1309de6b21bd4313f13e3d6d0aeb224d5e0,-0xe5af31c641a62ee0bae823386a355c04f35899f5267a20e4a9466b1092c,-0xf7652c8694420f6d3707548e5ea65b6032709452f564df3b8194b43d18,-0xe19988abdd97d57e2ba50a4a675dfa3d9493302409a11c153e7cb9907,-0xae5f14be6369c2a9946bea54144d5dc850285c999521cf0f32e2aba5,-0x7221ae0c8f4d2c5c7925df5b3d76f746172e36b609bd6d9e735d7b2,-0x3f11208578b61a71245e457577cdf6f11e8ce42974befe414a4586,-0x1d42c7d9fd0ff66ea4305bbdff76d2d2c9a3c2996bf98c77b5051,-0xb4dc3baa607431154a037ba9ef9eae4210e77bd2c624d901166,-0x3978b6278a69c3546f9f778594173968db60a4d303fc9de5d8,-0xec363c2e31ad523e3523ab012ef51ebca6f755a2514ed5b0,-0x2fd3e9542ae81e34a929e14c32a596f3f5a32cd49826459,-0x758e95a674113a717ca67254005cc6ddf3bb01c80b76d,-0xce04e033f4d59927a54d3277de29d919b7170a85aea,-0xe555a205f25face13fc283a33dc2c02f62396bfda,-0x79de045cac24d902d09065bc05e6443a8bfc5df]
def m31 : List ℤ := raw_ints% [0x0,-0xaa8bbbba7aee1e36a631b8bdac67503cb4af2d0d7c86143452dcdfadb710e2451000,0x13bf01771fecebc1578a249f816afd01de77ef9b0dc9f6740f02daa00b72e1e02d4c00,-0x11ba1f1054c7f61de81e1d92dde3e50a461a72333345fcb2d2e224e0109db8de5667800,0xa46202bac9fc7a6de7e693fc6d3943481bd8856260c3a6019758f18bced4556f5da0800,-0x4520829d43c20f30c220a7e1454a0c45efaaa4c3e23b563915401102a1ff7df57f47f200,0x1679f933d68c2c54f2503be62eb303e464ed3ff51c7be4a1b57aacfbf05331a7aff4836c0,-0x5e1421323ae1326d5b6f11746f0f1289e8aba83f99fc3edb74f4dc2cda8056d8d7ab1a4c0,0x14583a204202987c266bb2776deec9fe453ee648d91c9a9073d3450b440a42fbadad701b20,-0x3b54ffb02c806ac356c284755a0ef716dabd34ea9f679053c89e7d4dbe1dd9e8b503f91520,0x93f96e42990fe587f885a6769fe252eb699f42e921e869f1f693095506c58fac342b563dd0,-0x13f1ffb830f366269edd839ed73cb1e3f927041f43aa66f0869841106d450fa0ed5d6c00350,0x2584b2af1ab104969b666099239d2f8204ddc0d1a74b54e507b8ab8acac4e8f68903e057d28,-0x3df9ed14d85abfaa1eff6f90c96e0752e092e9bc2a021d9a2ce5af0dd98d5e36fb408e075e8,0x5a6378d8d032bac6adeb7dcdc1f14c5f93d61c45b1807781f9e5f39774f2fc3ad74c11eb390,-0x74e111291c56b87489bee71093a57f894f8b2d74143cb5cd919904e047aa964adbbf7a6a990,0x866f9a48da34b635091d0aa3b04ec080c04b4665da8a7ff49089a85551f150980c8cbf23864,-0x89e2d77405c7f2f0f82230c56ac02ae4023f73023c596635a93ef189a43e54ae5056428a844,0x7e55b9cef0c880dca400e62c4b02c72aeee012ad0a54e0f73ddbf26565a7c9033c466554254,-0x67853c86188939c66b7c56345bf4ba090c42a00e50639b0411e1734f5c3b980b751683b8274,0x4be867a70af4c8f9fcf2f8dce4e1328f52e12ab7885cf8d99e46442572ba1203f5226f86586,-0x31cfce6ed868e512cb268dd2fceae3e77fb833199e7c1e078a1124505555f50ba8da301af16,0x1d3d468824821b80c591a49861294bf375260ff76194eb2ebf390cccd775a0f3fd4cf2e63e4,-0xf56a8b5a8d539d0fb48f828fe962df0e819a655200f628fe44c4d3cb8daf306f3b6c055e64,0x72e2cb36d6ba4ee4f3a6b52236c94daf38ce8bb5e3698615db5ca930ac45c5e1749d2e5781,-0x2fe5feb6555bc3b510640f42968ab349f5dd92d28a0e32c5b7a837288b04c42caa370afaf9,0x11bd9f8e17db615a97c46796b75e856d08c0aeaf43278af0da73de2b5fbee020f5e710b4d8,-0x5d1ba07b8f04a951e15f7e8b39942f64f3177f90863fd2294114d3ee5ab28bde2bcaf61a8,0x1af243943f979631fbb7da1c58e55880e4348e02002e2b977c1363c91de21c3353eb7a8ac,-0x6d99edddea7fbed9f3f791c3629d0548fd790ac7c3c5ebd1e5f1d94011d0e22b2ea9f09c,0x185860da4c3587c3466392f7a22498c9ad811252202dc6497243dca3be90c3d28d371228,-0x4b236b504907d43394638cac72f821420c7974a7eb9692b38eef58a3ba423e79b4ccc38,0xc7f265e93dfa889089c5eb66f4bf7f91e73d0bbc4ac3cd0c534f0026620a9ff9f3ce13,-0x1c6e7ecd406680aee2e40df7b7b56f81708c7d70b0d087b282424ffd581452a96d2e6b,0x36c379b3c250c27028e7e5f53cbb4e386c6a2184d93a0815bc57e4dcdd1fe67721064,-0x5847556e19e270e2a7efea60bdb7af10a69401824d208a67bee09a28e5a7f9a7c2a4,0x757cfcd0b5da2a4a42e0f7c71b254946e0758bdef16b56bfba7e7fd895ac62ddc16,-0x7f091536f07aab3b639d4d5ea3e203545086234edafe24de3331de74673443d446,0x6d7a62694ff092d674d792d773eda4a923b72a31774a3c59668de54683820f574,-0x497c7d993c00d619c3b372530fbc253b64bf67a32c0ade9047efd4aaea491a14,0x255ce943529a03673eec76670eb1e7552756808a396dad95342e4dc41b989d7,-0xde78b16ea6396df0516c14c23c5fe72413b79c4ab3fe98b5302e11d8b5b7f,0x3a118002328a819da739e2eb6a8e6c2b3e212d966d6e5ff52bb2d8e6c720,-0xa120d3e492434be029d071ebdfce425b7b736a642ffc8525efceed3d70,0x114e13ae6c373763c761977f229247f28a1026d150f3c4ff8fa9c6ff0,-0x10c0bf68314d2e84f6865879fd56452da1db94ea3d07db307eac380,0x7feb53f42ab8560e9c12450d835adb73f86b62f8f621bc9439b0,-0x188f9021792938c595cdcd72673a4aacfac4643d783229f580,0x155eab18316104d3a3773a3491ef21c5dd16955bba435b1,-0x265a2243201bd678605b98cc1da61da573cf4cf2659]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 31
theorem quotient_ok_31 : quotientCheck 25 102 31 num den q31 r31=true := by decide +kernel
theorem quotient_source_31 (size : ℕ) : (coefficientsPoly q31).map (Int.castRingHom ℚ)=polyPart (key size) (X^31) :=
  quotient_from_check (key size) 102 31 num den q31 r31 (num_source size) (den_source size) quotient_ok_31
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_31 : cachedMomentCheck cache 59 indices rho q31 m31 31 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_31 (size : ℕ) : intPolyRF (coefficientsPoly m31)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^31) :=
  moment_from_cached_check cache (key size) 59 indices rho q31 m31 31 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_31 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<25 at hj;omega) moment_ok_31
def q32 : List ℤ := raw_ints% [-0x79de045cac24d902d09065bc05e6443a8bfc5df,0x2c7299c3f28e3a4a89c86df97f9bf809c5318b,-0xff7277009b928546f4f510276d716c47a82e,0x5a4316cc8201e674deee491296593d3c30e,-0x1f55bfceadab8e82fc7ff3baf39fb73ac6,0xaac1ae1be8b0fb427aeabeeb5632d20a,-0x38f784d6580e68eba7706c5e5fe852f,0x129532c9b60c95d55df764c59b28c7,-0x5ea4c91b4cdb1de15a5399b38831,0x1d54d618c251d41646b20336acd,-0x8d3c1d1cb2d43003026c3bfd4,0x292689dd7adc102f13d946e4,-0xb914b521b62bb020253560,0x31fd9df8d731bffb83914,-0xce964fa30267c0ca15d,0x32ba9ad06072605ca5,-0xbc2a5a79391fdd93,0x28d3de053b44e1f,-0x83380a9c7170a,0x180f6b575d4a,-0x3f3b0c6c0a,0x9101272e,-0x1172d1b,0x1a813,-0x1c5,0x1]
def r32 : List ℤ := raw_ints% [0x50dfec07e9b142b4096e979d5292b2dfd6270869c4280c4cfa2ef95d608f000000,0x6d07e8aac241224215f620deababae1641bbe2af174a6f417fd29a48b188480000,0x45f86406d9abdc54adac335c1a4ee6235cd943ff008f352b7634db79d5fcb48000,0x1c7305e6dcbd5f2c0fe0bb3b1fefa89e9b4461d2dddda12d842382ece4229d3000,0x83a88978f5dbfd4af7eafdb34abdf5ae13d7352b83643975f59bccc05d5d3e400,0x1cd55d9d2a50efa2b4456af18915079b0ef3c1f3b016059f14b9fc288f2f7d100,0x4f7f2446b97c3af9430b83d90db6ece073795f6b632fe29108e20f0ec5cbaa40,0xb0ea4295589a32b710484f674be4325e26a01ea71672d73e0bca842efef66c0,0x14373554c074ea7da9223e20d8e984cd70458e285936dc5e031a146c3584950,0x1ebe24cdbb794daf5ee1437e4426edc1a5d7260a5fe12929d34592381a4e70,0x27396dee6183df2e68713bdd6a49a8f6d0b0beb5711dd38ba50d4471c83fc,0x2a3a8df53da629b8ebebf980e4aa0c21cbee1e22e0ab9e863a94c3c3ff04,0x267d20beb7f2602f3fc46a8c7658d207d70551f601e7ef1fbb9a01cc67b,0x1dbb94bda2cb7e5e2d125cd0b497701f8f69fb08e59c532b320fc3b6f0,0x1373216041e30222840d33a9afea733f27a16e1f676a386e18e84cd15,0xabdaadaaecd586f0a530f7eed5cb04593ea9eec54b86e346b681a8c,0x4fae7db5bca76d55c1dba6da8bd2ad6e6d07d6069765982621f987,0x1ec28ee74d3448a916f30c3b069883d3f96121afc6da30e19fe30,0x9c460e924a9ca3c977812b793dd440318993d67c4ea9e7a6612,0x281c59ea5dc507ee598ddca09e93a4cd354038dba5d2e869dc,0x81d4c865e578d16b30bcff0f61c35a7d5abcca4e061c61ed,0x13ed08796c298ca69a9901098df6d3f1e3311679681cab0,0x22e28388c3cd51109b6f1ae3ec752c2c7fb80cf97e4e5,0x26ca4fcb3cb0c40ff42e7f05e02801416d11c126694,0x1496acec1aa7e42985f59cff5a5679bcaedb20a79]
def m32 : List ℤ := raw_ints% [0x0,0x15fc033309d8b1e50b6c68d073395157d34a94cebd0d489abeae78d564992d2ae71000,-0x2885d314a44fffd96b9d5e28c83ca9d3dad75e2fcc708c4f5ef5e2ea179cf1de5d6cc00,0x2430c72c015f953f4d51aceafca8a76547a329dfcc788932beb5f1f84fbab371cd67e000,-0x14dc9c0a3afb9572b33cf346ef40a020b736e30bf176b3cdae069f9224dca0080aa3a9600,0x8b94b975c151f2aff047def82ed5f8545fa0527e4de4a0be5d58ffa2585d0384f43fec800,-0x2d1ed95fe0c12f12d7654b3df3a143b51cc3668bfb01fc1ca758894d9db198d797aed36a40,0xbbb76564a19352f7a7b3748386305a56ff8600fc79382c356a337756c6a0500f39fed27440,-0x28569afeb59f621ccf5358ad5082ad61564253513633e4c96f6f39a3040d20553a9628bdba0,0x74de5d25651a56ee8d161409cd8c0db5e6aec43589f5367cdecdb2fdfae5b75f8430c0e01a0,-0x12179fc35399a9bf00677c5dc076a97f55f4d91e06446ac83c58e4a5ac75d62cb3f1fb61c3b0,0x26bd56571d5bd4131e4314e805d96d1a3c61aa73f0fc689f3fe725c92e036bdb0114071e9e30,-0x4853f458bed82b02715edcaa1923d35623718d10a7026cf8afc8201c0ad3a3e094ca84117ec8,0x768bc8c573ba7e83566f9b57f52610f13126ecfedbf38945eff5c16f3021fb80680accb92088,-0xab7b0ab7854e6a8c0ee61f2a0d14c64e2141837b2807cfb82a4d9105aaf12d09043a09a1d0f0,0xdbd741735b5174ed7553174edcc2c81e153a3bdcb72027008dcd4f902b72c695565c1fc5aff0,-0xfa988363be0f45abb54f4bef3a8da23f86156cb7987551e404499cd36f8c3a2738b65a274904,0xfe9b4c066dd49ae66ddf20a5651ae84b48dd12af9535389d8d43fd029feddb92d4791d7f81e4,-0xe6f7e61a9a713c2f62d74fecb94286665de93ac0e7880df4a3ec3388c9445e42838aa243a44c,0xbb498c4006a2c3e918269db3141bc2d7b8c0e44c79186339adf2a3b68a0452a6b3ef84c1cbac,-0x87d2f2b09df961ac07dd0a9b22677ab54ab139686a5e45a44f5d2d6c9f2583df31ea0299066e,0x581904b4cf1127bdc9c397843363b209a9386c2a084fed3a1b146ec9568c2b35c0081655e03e,-0x3314aa39240b834566917d50cb6817e448410c082636d417a3461a4822b9f3394d2ef757395c,0x1a73133181756ab7effe219ac50740669c30e0eb1b1a589640899b7eb039180f33fe2ec6971c,-0xc3648bb1bc081e8e73380ac68b114c808007fda79cf3ca8cb6a907e23d08ba837eefa02cb89,0x50476e3e8668c3bd843491f348440c4b5f00cbd751db095f4c2c3c75cb1240ceb9fcceefe41,-0x1d46472656cf92d3565ddfb1d3232bb5c34cefa9a61404b6ad8b9bac1d5dc2378c69ac30070,0x971d22aaf85656f18d9c548fa5ad343b92e78e4cfaa730a4e4b30a4a01809868dc126db180,-0x2af78fd312c70c76ed3bc6627577ef55115d10712a771fa92d8c71e4f94eda0030e93f6034,0xab7db4390cdf7dbed7eb1ab3624cc0c4deab9ef6afcca4597fd28f5a638a6151d79c45b64,-0x255448d2fd40916e54d6d6055c1b02ad40ee36a3a95666c383131e888a55075e0a24690c0,0x70bca8aac589fd45cd7ae8a58920a2908d163b182ff53ba8ce711645e3444249740da310,-0x12513a35fec2e292f5bc1088a7db60340dda52b80ce056ed412b0d020a1b8cb6bc3af5bb,0x28a3b1e881f3b3a09a2759d5f77b8f86dc1328002f5d0b246d448987026a25eabf8cc53,-0x4c2e7021733a1f19a65388ccbfedca59a28b446c2845bca0f880b27d6c1899d83b394c,0x77401414cf065a0342156c77f883586bdfe66d2f021d8575f468ea50599bb37061d4c,-0x99bc149b855f1055333404ca29ade7c4f453aa5a7daafcbdc2ba5f3d19be827c2c4e,0xa0937d0fc99c02d76ac0136971d09c1d61491c28a360dae316b6e957a48bd310d3e,-0x8544dbf3f90a8e73ba7e86221c0ca8c4cf1069cda1072cdc0a0a64bfb4c9826c5c,0x55db067c3605cdf6f4f6c321c983290d17b80d0c2a8e369b5f842279c616542bc,-0x29bc5008121ee4353f2ec88ae377d06b11833b53222690fccb70a450419ebbef,0xec97395fc72193716ec96f4e53961f2da70e223252cf6a1f41a26bdebcdf57,-0x3a83d2023b056009a05d5d389991bc94b47b9d72e89212145f726abfb98c8,0x990b8aa33857e7f8e4c5271d97fc3db756b751aa3b5ef03f3136465e4d8,-0xf672839df96b59aaf6bc530890439c8e831c3a57e5aa8c0c5360f95a8,0xde2199702079c27d02b4b42968d8df34e169827827328c5bcabdbf8,-0x61fbc8be3326899e17e6693addd04d3dad70b507a27d182436fd8,0x113f4aa5702456d951f91803ed8662e4f7966f7e3ef6b5b4968,-0xda097ce11e559b61b128944cb1947ea05c6052eab7138c9,0x15f313b7722da5e7ba41d4b91cecaa9da9cc16e8cd31]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 32
theorem quotient_ok_32 : quotientCheck 25 104 32 num den q32 r32=true := by decide +kernel
theorem quotient_source_32 (size : ℕ) : (coefficientsPoly q32).map (Int.castRingHom ℚ)=polyPart (key size) (X^32) :=
  quotient_from_check (key size) 104 32 num den q32 r32 (num_source size) (den_source size) quotient_ok_32
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_32 : cachedMomentCheck cache 59 indices rho q32 m32 32 135074531203053231585779343360000 33=true := by decide +kernel
theorem moment_source_32 (size : ℕ) : intPolyRF (coefficientsPoly m32)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^32) :=
  moment_from_cached_check cache (key size) 59 indices rho q32 m32 32 135074531203053231585779343360000 33 25
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_32 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<26 at hj;omega) moment_ok_32
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30,m31,m32]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<33) : intPolyRF (mz e)=rfPoly (C (135074531203053231585779343360000:ℚ))*rfX^33*(1-rfX)^25*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V9C34
