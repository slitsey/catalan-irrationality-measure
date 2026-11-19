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
namespace CatalanCore.Li2.NVMod.FamilySource.U6C24
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,6,24,size⟩
def bases : List ℕ := [1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]
def num : List ℤ := raw_ints% [0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0x2eb6f5c878d70c0000,0x3df114b7c4062ec000,0x266ed1bcb23a473000,0xed45259fede21a500,0x3fcf7cf2569afc600,0xcb437c65c257b770,0x1f0d42db30f42290,0x3b8ef60bb3372f8,0x5ae376db9eb1b8,0x6f3232ff0e147,0x6d575516d791,0x56395c7af24,0x3621d1761c,0x1ab16ebea,0xa1cd966,0x2d732c,0x8ea4,0x117,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0xa,-0xaf,0xe7,-0x3e9,0x9fc2,-0x4ae2f,0x7ccf9,-0x1537c4,0x29bbf8,-0x631e6d,0x6f6f76,-0x1dd948c,0xcbc48,-0x192c265,0x602919]
def rhoDenominators : List ℤ := raw_ints% [0x5d7a280,0x19230,0x2cb,0x8f,0x68,0xa,0x5,0x23,0x40,0x24,0x2d,0x37,0x6e,0x8f,0x3e9,0x41,0x2080,0x4510]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 25
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤24))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤24 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 25 omega7=padCoefficients 25 (omegaCoefficients 24 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 24 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 25 omega8=padCoefficients 25 (omegaCoefficients 24 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 24 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 25 omega9=padCoefficients 25 (omegaCoefficients 24 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 24 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 25 omega10=padCoefficients 25 (omegaCoefficients 24 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 24 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 25 omega11=padCoefficients 25 (omegaCoefficients 24 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 24 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 25 omega12=padCoefficients 25 (omegaCoefficients 24 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 24 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 25 omega13=padCoefficients 25 (omegaCoefficients 24 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 24 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 25 omega14=padCoefficients 25 (omegaCoefficients 24 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 24 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 25 omega15=padCoefficients 25 (omegaCoefficients 24 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 24 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 25 omega16=padCoefficients 25 (omegaCoefficients 24 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 24 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 25 omega17=padCoefficients 25 (omegaCoefficients 24 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 24 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 25 omega18=padCoefficients 25 (omegaCoefficients 24 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 24 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 25 omega19=padCoefficients 25 (omegaCoefficients 24 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 24 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 25 omega20=padCoefficients 25 (omegaCoefficients 24 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 24 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 25 omega21=padCoefficients 25 (omegaCoefficients 24 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 24 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 25 omega22=padCoefficients 25 (omegaCoefficients 24 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 24 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 25 omega23=padCoefficients 25 (omegaCoefficients 24 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 24 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 25 omega24=padCoefficients 25 (omegaCoefficients 24 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 24 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x10,0x78,-0x230,0x71c,-0x1110,0x1f48,-0x2cb0,0x3246,-0x2cb0,0x1f48,-0x1110,0x71c,-0x230,0x78,-0x10,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 18 li0=padCoefficients 18 (liCoefficients 17 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 17 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xf,0x69,-0x1c7,0x555,-0xbbb,0x138d,-0x1923,0x1923,-0x138d,0xbbb,-0x555,0x1c7,-0x69,0xf,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 18 li1=padCoefficients 18 (liCoefficients 17 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 17 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xd,0x4d,-0x111,0x27d,-0x3e9,0x3e9,-0x1ad,-0x1ad,0x3e9,-0x3e9,0x27d,-0x111,0x4d,-0xd,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 18 li2=padCoefficients 18 (liCoefficients 17 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 17 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x9,0x1b,0xd,-0x15f,0x507,-0xa9d,0xf15,-0xf15,0xa9d,-0x507,0x15f,-0xd,-0x1b,0x9,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 18 li3=padCoefficients 18 (liCoefficients 17 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 17 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x1,-0x37,0x177,-0x4bb,0x8fb,-0xa03,0x483,0x483,-0xa03,0x8fb,-0x4bb,0x177,-0x37,-0x1,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 18 li4=padCoefficients 18 (liCoefficients 17 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 17 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xf,-0xa5,0x235,-0x267,-0x549,0x176b,-0x289b,0x289b,-0x176b,0x549,0x267,-0x235,0xa5,-0xf,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 18 li5=padCoefficients 18 (liCoefficients 17 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 17 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2f,-0xdf,-0x111,0xf9d,-0x2ced,0x3cdd,-0x1dcd,-0x1dcd,0x3cdd,-0x2ced,0xf9d,-0x111,-0xdf,0x2f,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 18 li6=padCoefficients 18 (liCoefficients 17 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 17 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6f,0x93,-0xfe3,0x3051,-0x21e1,-0x6605,0x10c35,-0x10c35,0x6605,0x21e1,-0x3051,0xfe3,-0x93,-0x6f,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 18 li7=padCoefficients 18 (liCoefficients 17 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 17 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xef,0x929,-0x2e59,-0xb4b,0x16d3b,-0x2d193,0x193e3,0x193e3,-0x2d193,0x16d3b,-0xb4b,-0x2e59,0x929,0xef,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 18 li8=padCoefficients 18 (liCoefficients 17 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 17 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1ef,0x2b6b,-0xdbb,-0x2a0b7,0x56727,0x15dab,-0xe32fb,0xe32fb,-0x15dab,-0x56727,0x2a0b7,0xdbb,-0x2b6b,-0x1ef,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 18 li9=padCoefficients 18 (liCoefficients 17 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 17 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3ef,0xa331,0x2cc1f,-0xb09f3,-0xa279d,0x3ad6bd,-0x29186d,-0x29186d,0x3ad6bd,-0xa279d,-0xb09f3,0x2cc1f,0xa331,0x3ef,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 18 li10=padCoefficients 18 (liCoefficients 17 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 17 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7ef,0x22c83,0x1649ad,0x37581,-0xbdef91,0x6e3bdb,0x171dbd5,-0x171dbd5,-0x6e3bdb,0xbdef91,-0x37581,-0x1649ad,-0x22c83,-0x7ef,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 18 li11=padCoefficients 18 (liCoefficients 17 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 17 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfef,0x70c79,0x7ea257,0x1b1aba5,-0x2986fb5,-0x7be17f3,0x81f1d43,0x81f1d43,-0x7be17f3,-0x2986fb5,0x1b1aba5,0x7ea257,0x70c79,0xfef,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 18 li12=padCoefficients 18 (liCoefficients 17 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 17 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fef,0x16345b,0x2736c55,0x115a04f9,0x161b7277,-0x3ca401f5,-0x4918075b,0x4918075b,0x3ca401f5,-0x161b7277,-0x115a04f9,-0x2736c55,-0x16345b,-0x1fef,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 18 li13=padCoefficients 18 (liCoefficients 17 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 17 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fef,0x44bc01,0xb494a4f,0x81e7e37d,0x1d6c4cdf3,0x12176ab5d,-0x385b1a30d,-0x385b1a30d,0x12176ab5d,0x1d6c4cdf3,0x81e7e37d,0xb494a4f,0x44bc01,0x3fef,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 18 li14=padCoefficients 18 (liCoefficients 17 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 17 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fef,0xd272f3,0x31b9e43d,0x34dfa1bb1,0x146d75993f,0x309229223b,0x1fb33ebb75,-0x1fb33ebb75,-0x309229223b,-0x146d75993f,-0x34dfa1bb1,-0x31b9e43d,-0xd272f3,-0x7fef,-0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 18 li15=padCoefficients 18 (liCoefficients 17 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 17 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffef,0x27fd7c9,0xd4e9b207,0x13e13cd395,0xb619b7b75b,0x2eacce53cad,0x5ce1c766ea3,0x5ce1c766ea3,0x2eacce53cad,0xb619b7b75b,0x13e13cd395,0xd4e9b207,0x27fd7c9,0xffef,0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 18 li16=padCoefficients 18 (liCoefficients 17 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 17 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x11,0x88,-0x2a8,0x94c,-0x182c,0x3058,-0x4bf8,0x5ef6,-0x5ef6,0x4bf8,-0x3058,0x182c,-0x94c,0x2a8,-0x88,0x11,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 17 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^17 := by
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 24 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 7 25 at hb
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
theorem cache_li (j : ℕ) (hj : j<17) : coefficientsPoly (cache.li j)=liNumerator 17 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x587e632810c729e2a0635d5800,-0x8dde53e3daaa6b4b0e0dac48100,0x6d917991910f5ee52ce67eed5140,-0x3648920d0613e7006eb98f57755c0,0x1361691e2d365f6147b31f94d7fb90,-0x54f7edc0487958a3f41eef2446fc10,0x12953b4b01a94f79269a0e95a0dfac0,-0x3549cb22876e46b453b1a7a8b778b60,0x7f95e9cf7211e714c9173a1edb9c264,-0x1028d69f81b6ab3724e4af5fd989e904,0x1bffd92ded8f3894be9f14d175ce5de0,-0x29cb471b3a3ce6fa2aa49d8dee9d9c60,0x360aac7af7969e8e0e9cd51485845780,-0x3cc546bd82fb962c26522ade86928400,0x3b950b7a1cb7c8c7d7e90c2d51b4a3a0,-0x330058af9ef1422df109f51316778008,0x261f7fde80191c6e21706a705505ea59,-0x18dd10369e0ef700c2d1ba673f3136c1,0xe1eec65aea8cb6d434b9c3f4927ed28,-0x6f63ab35b6fa04d49575528ebb8fd68,0x2f76d11c80112d625e08b6bf3cc37ac,-0x1160b619bebf3837b6ab424464513ec,0x56cdb94d3efbde23b62b68d47f2838,-0x16e1f55646f6958ebe55340adbfcc8,0x507b3dd2b7408af2f6ad6df769aba,-0xe84178303caeaf44e71249f6700a,0x21a72f3493a4727fc1eef9f93338,-0x3cef1fa62227cb72ef46ce88ab8,0x52e34ef7325a4e0e8a8deb471c,-0x501caef3a90eed5897237799c,0x32873b5c3c93fed6503eab68,-0x120c35b1458e5faced7f470,0x2c7e7883455d2a72cd091,-0x17fad7992edbd2d2f19,0x2084567c7ed9300,-0x10422b3e3f6c980,0x640d58e1864d80,-0x1c96196501cd00,0x5b79eadcd2900,-0xb6f3d5b9a520,0xac30c927320]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 18 34 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 34 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 42 indices rho q0 m0 0 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 42 indices rho q0 m0 0 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x84bd94bc192abed3f0950c04000,0xd1b9dd94696e0239783228031900,-0x9f932f0281113cb614b667688eec0,0x4ddb0884844a9929809ae544ac06c0,-0x1b5cadac70316ef9f8aeea40478f470,0x7608d65abffbfd0f0e813594d620370,-0x196355225c54244637706a56bc5c9540,0x4790375fc4594b459566b6d7736e3640,-0xa8558164bec9ac2cc0be1e40a2e8819c,0x14ef31f67d65620c180fac92e9292fe5c,-0x2397f5dba659148d6ed49d606b3b87620,0x3419aac8c8f60399b028eb4abaa81cba0,-0x4203e3060adf780734d3f4914f4e72c80,0x48aff40ac1c840f7a67cdb45ad027ea00,-0x45b88891d723640832fe8842f2c7c3060,0x3a54efbc10e58b9e02601da566b6927a0,-0x2a92fbccaa21eb8288b4c6aa46f0a62a7,0x1b14c9f0bb2e2abf05c7ca905f1eb3cd7,-0xefb64ec661fcf255f4cc3d27dd0c5fd8,0x72f66ebf77cd7bba947ea82188409738,-0x2f93e26407572bd504e992c86e979d54,0x10e372154b2bbe9781798968d222cff4,-0x519fb3df2c66df95ff232ec0926c8c8,0x14c56bef911908bdbedbd548fb7b328,-0x4654ebf269ff904c8614d71649a166,0xc2c6a89d864c3189ff97af986aa26,-0x1afae1b4eb22dd4550ca82e376cc8,0x2e7b8c051b625d5f28dffce5e168,-0x3bcfdc0717d75f72c1095c81564,0x3645f38bcec1eb2e16cb98ac44,-0x1fd10dd1794cf7888756b7298,0xa6aaa31a0f47237142b9678,-0x17122c4f58803f46ee342f,0xad9eec5146d023ea57f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 18 35 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 35 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 42 indices rho q1 m1 1 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 42 indices rho q1 m1 1 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,0xc71c5f1a25c01e3de8df92060000,-0x1362a9600a633af2efac5da0db6f00,0xe89793aeb0f1d3b053cd3418c4a340,-0x6fcc5fad83b62eac987cc23ef125740,0x26b1414dc281f2fe8f1961da220d7210,-0xa44b760ca97a6a00c67ffa614ff69f10,0x22c47a3675f5795c2913b7420d96f38c0,-0x605ed2d21d04c97f77da2f93de04b2ec0,0xdeca5d81b319af04a6bff9111498f1404,-0x1b36f12c11b83f333ed23c9744a4532244,0x2d6bd8a82bd71d8a54b844d05d4bf830e0,-0x413834996af0587cb257cbea2a4fc15f60,0x51015f2b11c66d3a3bd78c8ec90f2c5680,-0x575c47b9d12d27746a810d75d521677d00,0x5200b8fea5a5fa32862445614c3c7e84a0,-0x43138daf4bc6c0422d170152f226766520,0x2fd06a4fae61ab251b2f822dcced91f781,-0x1daba4a7ee97c176fb3c4905e7c4816611,0xffe1a7c23c996f0a9a3460ddb529f1068,-0x77649c94a6ca8480ea7252d9eb358d908,0x2ffeed843862058e7ed9c5ee9a13f328c,-0x1084d4c3100e53251ac1d5988e7040bec,0x4d3ff7909b8ed4034680d0e2ccac95f8,-0x12f9bdb2bde360168943756c0f57a418,0x3dd91bca1347a70a6282983b3b90e2a,-0xa454dfa25c4b02f210f9a9212437ea,0x15c0c76a2637dfa412857182ca2df8,-0x23a452010308523056ca65edb9758,0x2b5a863bd4ee4aecb36bb79884fc,-0x24e64cbdae111bca25c40ca681c,0x141538545374303ba5555ce3a8,-0x604ce02f0b743c355b1dea88,0xbf5f3f46778811495e1cb9,-0x4e8657e9716b3c2cf729]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 18 36 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 36 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 42 indices rho q2 m2 2 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 42 indices rho q2 m2 2 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x12aaa8ea738a02d5cdd4f5b0900000,0x1cae452d9e4e29dce15790a419b7900,-0x1534a23126c8aa921d5324656a672ac0,0xa0bad4ec027f9a79b4ff6a9787d776c0,-0x36cd038fdbb91f2d3e7df369f0351df70,0xe52230745bade2be8fac11685140eca70,-0x2fb9344f71422dd200e37230add8ac1940,0x8220d59b6a9e8ef01aa7ad679f761b1b40,-0x127c517caf5479314d964af658a6699445c,0x23800fd4e0eff753a255bf283411bc4541c,-0x3a2e64fbbe5af4ad38a0e86221159041820,0x51fa5592ffcf7921bd85590ee46ad7685a0,-0x63d6fe3fe36960cca2524564fd0fcb2d680,0x697e3e19d6a418593ef167a6ccd098d1c00,-0x60eef2c01793088e104fca13ff516561660,0x4d8a66ee0b985ab9b7a651610c954410be0,-0x35ff3539f9a79a85b4ef328d6db014685d7,0x20b1e29d3fe7b04d74dd981ab6bf956fec7,-0x112c501e1da5204799aa2587cf40b964358,0x7cc0a5450af5a8bf284ba4bd57b4e379b8,-0x30b821f3df68cafe4438a2d907740f4f94,0x10425277737aefc1e7ccf461cf604fa734,-0x4992251ec13518ea2a8e8f6564eb9e748,0x11717889b2feb5534d40264d2caa08828,-0x36b8052d2d60e45d8025f1dfe222e546,0x8b747e1b0dc0e34f64055577ad1a186,-0x11a273e9ae544723493a4c8457dc348,0x1b76eead6dbf197d635c11be063ae8,-0x1f8eb9cdbc3b7223c5c991c12baa4,0x192bdc7e82daae49f2c1909fb284,-0xcb45ebff0d46d7ad79adbf1a18,0x37b1c98b2cf376e538cb61a38,-0x633128363d4a5114b5715df,0x237ee41754e3a2c0cd7ef]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 18 37 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 37 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 42 indices rho q3 m3 3 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 42 indices rho q3 m3 3 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x1bfffd5fad4f0440b4bf7088d800000,-0x2a732dfeea9fa3dd01258eff3263df00,0x1ef5206af9c85e2e757a44f2b3b50d740,-0xe75904eed5e498df8c15b07a218b6ab40,0x4dbc68d965b604e5d121cc0f6fbbc31310,-0x1402d60acbdee0470340eeeb0c8a3083010,0x41a877d64dd617c3dcab6a1c801f8c744c0,-0xb02df2d3174486f2ee34faacfdd78fc32c0,0x189d77e414b455f126f50669be7bacf89444,-0x2e76ed3b960f8d1dbdfd0e6dbb1c11e18e84,0x4acd5e606661dd14e4d5e6c4f976aea596e0,-0x6775503a7e93eb934ead1eeb574d542dad60,0x7b96c404d31d1ce1a956d93cbd0b0497d480,-0x7ffb61d8d25cf02a1f683733a0fd99390300,0x7325d304c66e10dc9068771e089a18acd6a0,-0x5a1a693eeeccf4c0418e181e96caf950f520,0x3d4f897f32dbb093777e96fc9152e6c23b11,-0x243b28490cf2a04ded0b253c4dabbf6924a1,0x128c5d5f97873f84239de01bd90ae3e172e8,-0x8321cb078304dbf9778c96dcb44089a8d88,0x31c124fe17c4a55c5d25a09a60d52b6494c,-0x101a0113801e6528820c9440bbc2c3f10ac,0x467f2eba805e2e55f12024f74ad2e7a978,-0x1021be28e280f97c6ed6627eb01250d598,0x30b2681b753330f9818d0626fd18895ca,-0x7702f03f8ec7381c728719956d026f8a,0xe5ef7e8c54eb91c4b67a70f42f11978,-0x15436c77ce07019417ae397b6f140d8,0x171039d8959e95c7df11ed68d924bc,-0x11396f10fc333795e87b5906311dc,0x80d9ec6bc31d45310577e986228,-0x203c673b39a5aba7acc6eefd08,0x336660fc622b0aee105223c9,-0x100965cda1a840112b8739]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 18 38 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 38 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 42 indices rho q4 m4 4 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 42 indices rho q4 m4 4 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0x2eb6f5c878d70c0000,-0x3df114b7c4062ec000,-0x266ed1bcb23a473000,-0xed45259fede21a500,-0x3fcf7cf2569afc600,-0xcb437c65c257b770,-0x1f0d42db30ec3990,-0x3b8ef60bb0cb078,-0x5ae376db4b87a8,-0x6f3232f894e27,-0x6d5754c32fb9,-0x56395995ffc,-0x3621bf6483,-0x1ab11e6d0,-0xa1bdc7f,-0x2d50b8,-0x8b8d,-0xed]
def m5 : List ℤ := raw_ints% [0x0,-0x29fffc0f83f686610f1f28cd44000000,0x3eda91f273dc6714ed79842bcc9190900,-0x2d3a9d6681d2b5151d798831b0b9a356c0,0x14d602068ff9b6d4e468e83d6059c7d62c0,-0x6e7030862da7ff904284e33994ee47bb670,0x1c03ebd958655ae86541803f3c8070c45170,-0x5a8975a3cdafdf9e3aaf7501822f531aad40,0xef27252c7192b8dfac1e16eec9abc79e0f40,-0x20dfd9eca4ef03f18835a2e84c5235c6b621c,0x3d0447a4de969ca763405988a74f3bcec0ddc,-0x6085a25b1178f8609a2dbabb4b2d9310bc220,0x8315bbaa4c7785450f36dffeea526923707a0,-0x99a41da7cebc803e2280aac86e9423e30a880,0x9bf94e2eb697d9c69def0317831b84821e600,-0x897267bc692c72baa4b6fc077bc2c8d49b460,0x693c0def56c894cb81929b85bfa0d98d6d1e0,-0x45fc6eb4dfb4ae0eda2a1323f6b83947ac5c7,0x285f38aaafd6ec6680bf449468d21028b85b7,-0x1425e1fb4767b7a0a589c04c35bba41c50cd8,0x8aa4bb2148b4b199bb29182a6244753f7938,-0x331d101e0f326f95002df401e445d4ac42d4,0x100a825ac70d854a98abe5c550b1b7310474,-0x43f4587e785d0e440403e0fd5854746f7c8,0xf01ba9f815c00c55354883c216e4a496a8,-0x2b95d6868539ba70314e9acd4de311c0a6,0x661e1315dddac713dfaa3bd0ae16a00e6,-0xbc53ce7bc332570d1ca72d11c4e1fbc8,0x10895b4bb5c7216c592c26a34c7ddd68,-0x10eb6b4f872cbe468828bb3d0db9ce4,0xbd2114b8f377abf520ff7892c02c4,-0x51d3665637c0947c2700f84a6798,0x12aba6be5268a48637a6d00a9b8,-0x1aa07b7c159ffd51fd1c2f64f,0x73dd8a11add887bd71415f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 18 40 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 40 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 42 indices rho q5 m5 5 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 42 indices rho q5 m5 5 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0xed,0x1]
def r6 : List ℤ := raw_ints% [0x2b3f618a97df161c0000,0x392979385800e23bc000,0x2356a716f93bedb8b000,0xd94216b94416ade9100,0x3a25d186ba3f998a900,0xb830825b0f81850cb0,0x1bf40368868fac47e0,0x3532859b21db53608,0x506ba5a896ddd6e0,0x614341c86b50713,0x5e46b6969c4316,0x48fda5519f49b,0x2cb9b950f7f0,0x1554279031f,0x7b1a35c9e,0x1ff7c33d,0x56bd1c,0x76be]
def m6 : List ℤ := raw_ints% [0x0,0x3efffa1745f1c99196aebd33e60000000,-0x5d19b18a8a6f3578ef1bf7ea64443fcf00,0x422130d30a5e4726703e1d175b40c2ccb40,-0x1e0f15d21663cd02c857d2d5e4f90acfdf40,0x9d2225820e728f31542934360e2a579e6410,-0x274b5aa234116b99716af1f9dc3080e395110,0x7d1ed987f24ae6716c0329e4308623f3490c0,-0x14578ca0bc718cf577a430fa9b27f0cc365ec0,0x2c088433b87968a315ed59ea5d6f090ebf0084,-0x50632957a305a0afd827e880d319a39e6a3ec4,0x7cfe984799542f9270f1bf08a19ae6c43f5ce0,-0xa6bc5b6ba300bdc47b05e67a7e33a7b3385b60,0xbfcd66111327800b11f0435c51a3b7a0f93280,-0xbef0aa3d6cdeaea630f6a8ec4980b00c74a900,0xa4d805046149623eea03cd93991bed3ad888a0,-0x7b857e9c0bc495ec48c3f48fb30f1b20e84f20,0x504e683bfa2bd48d37a806d36656dd20f691a1,-0x2d3adef19f98e4ba62b1a132e70554b4944c31,0x16020586274a4e09539e9556955064a4114d68,-0x936c526c9cc568000e162e6af5fe1dcb08208,0x34d07ab8af6ae30ab548117fe89e28c22440c,-0x1012f3ccc177aae65231de814a641df2a516c,0x41e2703e006c31e63f12a89be8545eb364f8,-0xe0a39e4a6941ce2fe2bd225d34521fd8318,0x2739e233dc0e9173d1fdce3b7cd733f1b6a,-0x5814e3888442179c0cafc224dca361312a,0x9afeea1242e0c3e605762179a9a34ecf8,-0xcea6f30a0b066961768dfdf5567c5a58,0xc74fb0c7779600045456add31c0187c,-0x8224d8e8e05e48185b1a1a0bb2a79c,0x340c5f279703b7b5fa1d1ad6e98a8,-0xad1cc912dea6774b802e6103188,0xdca06d40b2c3f42bf8bbce5d9,-0x344b718139af649b3810849]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 18 42 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 42 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 42 indices rho q6 m6 6 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 42 indices rho q6 m6 6 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x76be,-0xed,0x1]
def r7 : List ℤ := raw_ints% [-0x15ab0114d27ccf22e80000,-0x1c8fd9188a26770d168000,-0x119a71736bdb232eb9e000,-0x6bd88e3834c50714dc600,-0x1cbfbd7fb683a0ada6300,-0x5aa59a54cf76b20f1c20,-0xdaef8264c2f5b9afa30,-0x19e0d94d78e17815c30,-0x26d52541c007fd8088,-0x2e8cf068e05c015d2,-0x2ca333ed279bcc8b,-0x221a03c9e5251a2,-0x148be950cc9c2d,-0x995fd26ffbbc,-0x35b8b255a95,-0xd632e660a,-0x2231b27b,-0x2aabf6]
def m7 : List ℤ := raw_ints% [0x0,-0x5e7ff722e8eaae5a62061bcdd900000000,0x89f42ed42cd36ece1e542342156e9bb9900,-0x60c2c28636fc3c34b1be721c7376fd0642c0,0x2b69a2a8d94eb2bfc7b290af7d29367090ec0,-0xdfe6e567544e021c2bf68a71615fc67affd70,0x373725a3063fa321be40c2eaf3e6b4fa024870,-0xad4ada42b45e27d81d96dba4751c686ab08140,0x1bc115e40372c53576ca4f936164c1f7ffe0340,-0x3b262d81ac29d0cc3afd93dc3013fda96439bdc,0x6a3f0dfa355604b9ac2ab4ca324cd6cec69639c,-0xa26f7f26b10e9cc28481e9fa85682a5f8ea8c20,0xd4e4e369742ab99fdfb726f16a17db8031da9a0,-0xf06dc8f30a8471911f68599611b99c24b5f1a80,0xeac60ed790f39e76e4ec3feeee949ecbe62d000,-0xc69f97bee39b0962a1910eef0246885319c3260,0x91b26e8650c1077594993cbda3dd583f74ae7e0,-0x5c9ec569752ddc9f545ec1bad8b9600990084b7,0x32f110e3eea072b6716f03a2f2348d767730ba7,-0x182bc5cd55751121f066e7b8015704459046e58,0x9da293bd467cb494963984ab8d075b59b830b8,-0x36e18efea99a77af43aa8daf0d5e09e95e6a14,0x1032e3041560cb4b97fafadf7e3170cfe375b4,-0x403d3044232a5f31aec89c6180092fe641048,0xd3554f192eaa877635fbe5e390e242736d28,-0x237df4bf31048a55b171743ba3a15f1f9206,0x4c5c09e394e15f4cd0d4bd92c11e6b53646,-0x8027ff0b48ffc101cfa16c452f39ed3c48,0xa2108decf684095763213670bf31867e8,-0x933cc28fd1fd8e87fe24c8bd20a22324,0x59c74fba797e71af309245f00221704,-0x21280070b4ef6a83e661d320c08d18,0x645cbae3d40e65c468c233202138,-0x72372f831ea5965f4ab3a3ddbf,0x17976617f87b4bf0f2df51cf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 18 44 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 44 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 42 indices rho q7 m7 7 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 42 indices rho q7 m7 7 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x2aabf6,0x76be,-0xed,0x1]
def r8 : List ℤ := raw_ints% [0x7c9656ce0eaa3bba9880000,0xa3d7df391ff0d5b88448000,0x64b6f847349c9686061a000,0x267312459a44fabd0d1ae00,0xa370edb61f161202dc7e00,0x20159ff7a7fcc36557b2a0,0x4d2631007e0eb17404a40,0x912869540e40c2512820,0xd88513229651be352a0,0x101b9b6c09ae59b66b2,0xf50f756f35dfaea84,0xb9521193e42b8c0d,0x6e448bc2b71e146,0x32a4bc1b3364af,0x11626d53c0e48,0x437e1adb5b3,0xa638a378e,0xc4fb69f]
def m8 : List ℤ := raw_ints% [0x0,0x8dbff2b45d600587930929b4c5800000000,-0xcc7de2bc892d4a30b582d900b6c1bfdabf00,0x8daf0f1241cb65b8b587ceab51904f98fff40,-0x3ec46c0005ee6678aaaee4dc959cfcc31c5340,0x13f81083bbcb54c75c4c1c8c167d58b2228c510,-0x4dba210498bca9cb6535fd5dcf1061c7f228210,0xf086b007caa187bec6fab0a5ebb8b5c463e9cc0,-0x25f629acb8ee788e2fb008ae5102f272bce14ac0,0x4fad94442d1c4d00260d1dd2cf5d1caa1e4fb0c4,-0x8cdd6ba686a15043c4bad8f7ccd9eafe564c7304,0xd3d243159f20c3b084d18875a79860475b0582e0,-0x110da31763aa026b5136629123fe20a6c1d34e960,0x12e9a5fd4367166770194545526075a815c00f080,-0x121eac3a2fb23afe349d292cdb4107695dfe32f00,0xf06b897f127b6f7eb7fc999ed5ba788cb1ef5aa0,-0xacae2804625bf8cf1f6fb2319a7cd54dc4ebc920,0x6b5bd0ace9b3a2ab2c3230915abbcdb2ffd34131,-0x39ac587410969a95bc10be4ad9d730a220dd5cc1,0x1ab057424bcd87cc131d58c8a55b8b042e65cfe8,-0xa979d8e64d61b014e0ee32cb0de0829fc36be88,0x39582a3a4dd6234ec75aff7d175f3c26411aacc,-0x106a45e11402bbe22a68105cbab538ae6715e2c,0x3efac39dd623b7a0144e3ac86d59eede2ed878,-0xc7e30dc6bf256a50f14120a78abfe188c0898,0x2047a73f7fe29b226505b7289274a4e179b0a,-0x42853b7d8d2eef77d4346b68e09c3bb5acca,0x6a6fb04dbdeca7415be5c2383663cd4f878,-0x7f978c72f445fd6c926e85c3e5c89b0bd8,0x6d1d3afa48602928df4af194199c6883c,-0x3e136723182180b9274d4ddbf67fd95c,0x15263e6dd2c717b44e07dc279c63728,-0x3a347cdecc0588d828c814c372e08,0x3b1b3a419124c1832bfee2d38e9,-0xaa341121d00eec50abf88a59]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 18 46 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 46 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 42 indices rho q8 m8 8 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 42 indices rho q8 m8 8 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r9 : List ℤ := raw_ints% [-0x23f1f4e54e68c58a418740000,-0x2f2cd28727b60f4d6aa014000,-0x1ceebf445f4272cfd16125000,-0xb0468645afe76ded6cd1db00,-0x2eb2555c9f09cc39e41e4c00,-0x92303baabbe9af6e9981090,-0x15e34c0a70beb22fd4c24d0,-0x29018f21a3bf83dbf86dc8,-0x3cdce30ceef01ef600928,-0x48075214f36fc3ca1279,-0x4406a3993488294925d,-0x3307a163375baa74d8,-0x1e11ecd42c988b757,-0xda5c71128b90110,-0x49db928dc025ab,-0x119663173c20c,-0x2a438af7a29,-0x30755cfbb]
def m9 : List ℤ := raw_ints% [0x0,-0xd49fec0e8c10084b5c8dbe8f284000000000,0x12f3b4510524d2302a3caf16b9aa2a3ca72900,-0xcf9cbf9ceed3fea11073f48ecbf42d3fefeec0,0x5ad91f96bb639dcf8b4e54a69c3602a71477ac0,-0x1c8934e6a9d27c2f516c8637ce6ad8467476b470,0x6d9c438c2d0c6c191ab2143d8480e67bcbf5af70,-0x14e8c9c6b5eb60af92e6e1b0c6e6dd4fe38e79540,0x340cbd7b9b50d3df0805d7d76fcb493f550993740,-0x6ba112234bd25a589531d15cf458c024b0a85f19c,0xbb570be0be38061775d4b4cbca531b442be64955c,-0x11528ea3ca5444d577af6a19178dd8c6eb86b8f620,0x15efcd2f8a84f0d74a0876a3b2148e107bdf536ba0,-0x17e5e66a84c75ac50057048d519bfd4763dc3d2c80,0x16787e743094333a1089a9db3030baaf83f5dada00,-0x12451a2f9f8c04c1d7f50b161a62a378341aa69060,0xcda0749bca717f30e42abe0628eb126642b905de0,-0x7d0e1b8a9c8734af56b967a0977e1ea2851a0c2a7,0x41a096df6d2da49251060bc3a291dccbab1ae8097,-0x1d9f9bae89609035af3092bed95c8a6684aa6e7d8,0xb72e49877b0ac14b8d9504f887f9d66df6c96038,-0x3c3e0940afc4b3c2db6b2f84b1efefb2859d4554,0x10b975f91205141c9b3d4893e2eacc59f2a33af4,-0x3e1364cb5e266c00c6051d74c143478fe68b0c8,0xbe0cbc91dd13d2c8da7182a65982238891aba8,-0x1d817a3bde6de9a7dbd3ceb4fae4c687c5d966,0x3a38b51a35228744d0f886b8a9fc0721f21a6,-0x58c6441863dd5a1e6c2792b4e8df857684c8,0x64d2bfc8002a7f0f08794f646f77b539a68,-0x511a61430e63daca6021f734f5dc15cd64,0x2b032f270c315dfce9eb48c69f1922f44,-0xd81a409b3c9373d7c9ed51945350a98,0x21c3bc9f655816cc1122dce33f10b8,-0x1e936a5d7f32795f8c21d2554c2f,0x4cb671944a70cc4022709793f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 18 48 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 48 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 42 indices rho q9 m9 9 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 42 indices rho q9 m9 9 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r10 : List ℤ := raw_ints% [0x8d7b8ab991c5c7e123c9c40000,0xb95a79b90d66faf951f8f24000,0x717391c51f4502da6c67ced000,0x2b1ad1e2082edd417b29ec3700,0xb63e1e89283fb5aa2a5adc700,0x238eb1a93c9f96db3f77842d0,0x54e88a447ffacd6caa7f9ea0,0x9e7e759ec7111064f975e58,0xea4384f801db98ecbf2ba0,0x113e95b3af446e994feeb5,0x10320b73bf0566658a372,0xc11dea621157fda78ef,0x70eae4e0c6b223759c,0x32c62c01a73a9d297,0x10faf2db87014672,0x3fcb53c52f8f79,0x969c1abf0bc0,0xa8c5d5eaa4]
def m10 : List ℤ := raw_ints% [0x0,0x13eefe215d2180c710ad49dd6bc60000000000,-0x1c1cea9f969f8eedeb9c201428c2bfb7304af00,0x1306eddb19759f4647d4c5498ca92be2f68e7340,-0x83a15818f58762b0e357acdb982f373eb8d80740,0x28d5d0f1e81bac0ab585fb891c493569d607b3610,-0x9ad72f0259f122b5eb95bf3ece6dae75a70e0c310,0x1d24a484d90a5061e18fa5f67f67d02c03080d68c0,-0x47899ae5231e8d2538cb15c21646449ef04f0ef6c0,0x91c7eed11346addcae23b903d4066642411a44e504,-0xf9e7631a65294d8ffa5150192a6644ab83db236b44,0x16bdc9b5374ac68fd3ef52711fa509aa239a12108e0,-0x1c52278774337717326d1cb48e6160dde096bd95760,0x1e50bc6170f09b38a7b728a39f9f62a0ef74f8f0e80,-0x1bfb777413bd83878e1641d8cbd327b1c5944f89500,0x164fcd0f7ca5d715ef5fdc97d5614f448ddaf7f4ca0,-0xf5fe39bae00f80037b1a2e7d86a235ba580042e320,0x925f373c7c6bc283862af66daf26fd335a275959c1,-0x4b0d38afede8d77703cf27776809181131859ee651,0x210cb47c003df5d2b533bc231eea4ae10cf6b77a68,-0xc707a5a8570962ae48b218bc43f7b1154bb3bc308,0x3f9f02332d009638e01571ff38b7a83da526b3d8c,-0x11212eede4b09fc52e082c34e1ce76de1ea9ef6ec,0x3d8111663fe2b76d1a0d80e98f8c6660f53583f8,-0xb59d48ba22fc7785a1969421c30c073945ce618,0x1b19d6b5ef67c68ee491a6dea45e87dd292b4aa,-0x333044558d3dfe4fa5df89f9caab548bd0826a,0x4a5879fb4c4741e117dda5e2f084f0383bbf8,-0x4ff32c57a44aba49b3d50c39d1f13a18d558,0x3c737ce68bbc209019525f67ae18ca633fc,-0x1ddc915a33e3b75ff4d65a6a73718c671c,0x8a268139f26ccaa855c6e490791dbda8,-0x13971acb45b4103303c42921b15f288,0xfcf8f33476a926b8e6e60c95acf9,-0x228f69065528ad21afdd461d69]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 18 50 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 50 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 42 indices rho q10 m10 10 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 42 indices rho q10 m10 10 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r11 : List ℤ := raw_ints% [-0x1ecc2b1fbe3bc89a0af6bbb00000,-0x284898552cc4690024bca7af0000,-0x189d128ef08ab3b7974b5e888000,-0x9555840e97bce14c1dbef90e400,-0x275fccde2e4e30ac7b4f3aaa100,-0x7a9d7c8263bbbdeed6d8601cc0,-0x123fc7ec35a6e409b01e558170,-0x21f54f9b4629ac3afc9e4b840,-0x32039ba33abdc669e69cab88,-0x3aaaa7b3cef28230a8f0bdc,-0x36d739b5aa7256bb01b42f,-0x28a63b6ddc2e9809e779e,-0x179e2811520c7196c901,-0xa8a63375db37e1904c,-0x37e5c9166c566aec1,-0xcfbc19fd0feb9be,-0x1e3e87a001b997,-0x21538163acfc]
def m11 : List ℤ := raw_ints% [0x0,-0x1de67d320bb2412a9903eecc21a900000000000,0x29b77466175d4ea30907c4b237652817556bb900,-0x1beb706a2be28990626a071742cdcefd4f6cc5ac0,0xbeea9e48ba3512ce7e4a42983bdc8bf853544a6c0,-0x3a83ffcb06bea8111c1186a450292a6141a336db70,0xdb1b7a3c96a2cbc791ef48d90e10956982c0bd8670,-0x28b3abfce9af7f6748e14a97ad300071a3ce0dbe940,0x628d987705825d1c767c9f1fce1005c71c395d3ab40,-0xc5fbdad7d747dde30fa57b0140def7cc2833354235c,0x14e5a8f26736f0c113db69a8cee4c3c4fc624d7d631c,-0x1df3ff69b908579596fdb5f1d5d4278b7b20c0f30020,0x24b1772d2166c5293cf5cb0a7c71ccbb26b3c9324da0,-0x269a7138ea5a48a7b47e44fe196bf7fe3399ef52de80,0x22fcfdcd2bd698085901d850f15d680da62dfe860400,-0x1b5d94e9cb2bb1deeaf41226b4d9f256f6d61282ce60,0x1279ee7ebcb83feeeefc85737b834a1bddc5a36933e0,-0xac224141077ae0ec10a20507d736376171347696f97,0x563ff866fb0f8b6b6bf0c32d1e236b25e9dd714d487,-0x250eb73bcd93b41f15d8a2744e8c1e82376958bf958,0xd95b75a54e94cf81673d03ce0d91c78b862aaa87b8,-0x43894d3b5c5bbd6c8ee31f798bd93804cdea321494,0x11a28f72e1cff485e2c98aa2e1bcbfc10f39359434,-0x3d3f4e90fb36f3578e858b10cb166c6ff4e475948,0xae68a9906fc8f42013e07c6384a80bece1add228,-0x190246f7978674f304f4b7f348b92ef00d29f6c6,0x2d337b69ffcdb8d3bb7dadbe32d897f51092306,-0x3e813ce6a58c4a9a07b776b389977271365548,0x3f9bc831c9d44d521e87fb19dc23d41a1f4e8,-0x2d2cf6a8135750206b5c6333753aa4b4dba4,0x14c4c49295f3d406d4d0c43afd51e6a8b84,-0x5865bcff39e3f2d5594624d843b676018,0xb5e16a71ebcdf025dd9a0185ee0f838,-0x82c297190c55dc215a01e07e3b19f,0xf9032cf6de2dddd647265127af]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 18 52 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 52 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 42 indices rho q11 m11 11 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 42 indices rho q11 m11 11 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r12 : List ℤ := raw_ints% [0x614d29ce9bee0ec9ebd13bfd00000,0x7f17bf8e1a1ae5316c0fb03550000,0x4d889cbcc7e0372cc52941aa44000,0x1d597e081b82c387c96fdb471ec00,0x7b93a1d1775f9744edb9c47e0400,0x180003d8b6483e564fb4aa3d3140,0x390392031c96445de554cdaa900,0x69cdeacbf0e83a278b27764ab0,0x9b5a308268caf3d7377e1d8e0,0xb598452cd15c51200751ca5c,0xa914210dfcb26787ed592e0,0x7cc117df47bc78be26e341,0x481a09c6358b14dc09bf2,0x1ffb1ca32c2784f8a957,0xa85e49a5c09706f81c,0x26c4f6a98a6bc408f,0x595e9a45ccfdfb2,0x6137a639fcd0d]
def m12 : List ℤ := raw_ints% [0x0,0x2cd9bbcb118b61bfe585e632327d800000000000,-0x3dec8c03c7da0acde67e2ca00ad538618acad9f00,0x28ff02f41e07a4fc37e18cf3dc9289e2d40c5c2740,-0x1152f7008c688145ad394e1210926c9b8f00436fb40,0x53f6b649470923ea86415ef56468f763d3860f6b710,-0x13690ec88a56ce503f02812ab175f0009a06c0551410,0x38f550eda84abb80a1ea871a9ead3f0976303c3cf4c0,-0x8815a8b9927ea0fb24de130e5436f014e8fe61cb62c0,0x10d95a4b32250f1d50a6933f231ad703f55e31696dd44,-0x1c0a621fc20810ae7de057809458a8b653a0da8176784,0x27942448afc6116dea59f8df9bac266ccc6502bc3eee0,-0x2fb4ec358c820e8ae1b566628614198f20893f683a560,0x31578bb8f53a8894b2c448c215d9f18911bfd06fb8c80,-0x2bec84034e13658a1e226a405d73ada813b1217f4db00,0x21b4e8cc1877150441196bf98725df095576b7e225ea0,-0x164d834392a245ab69ead45c5ef00a8f96ed65dff9d20,0xcb5ec9bef6c8fad8aaa7d09d811bb9cbdfd058c56b51,-0x639855dbe1b29820e12b37befff2e73cbf72b82678e1,0x29c18ccce4b64188917c7e03f3ba36cd386b8a30cce8,-0xee8fb53e8312ae46e8ef6fe080638fc00f9b0e40f88,0x480dde75979e0a1c156c42fc1fb4d3d6d8bfed7bc4c,-0x123f1ce186af6f1ab0b9348f47619ad88f21a99dbac,0x3d4afaff889167ca5cb12587f2224920e456c2e778,-0xa84a4756c0d9582a3dd538b605b3071df68259b98,0x172eda26a66dc3d72045c32dd87292cb15e00084a,-0x2814c549472c2c7122eb9cf12d7eed972eb1520a,0x34bee6d284e6169b15d506838dc565e00b8b778,-0x32c42b44a39c1463965e33f7d2f3341bcf36d8,0x21d7a8a5cfbbb9b747d10eb6c17a53712dbbc,-0xe77d3feea5991783b0e1b21002bee6610dc,0x389b6cdd04c80d6ade94e005037293ac28,-0x698b486f145ca75228eba1e53ea0ff08,0x438fdd463a85fa8031db31fc045209,-0x7017084784f39e2dabc6316d179]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 18 54 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 54 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 42 indices rho q12 m12 12 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 42 indices rho q12 m12 12 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r13 : List ℤ := raw_ints% [-0x11bd7ac4fc1a5e4b9f326cb879c0000,-0x172482b3a16e239c441fc1d404fc000,-0xe19407c9199c2e8f632683c3b87000,-0x55423d61771d72f5edf2f299322100,-0x1665e57a28656a3e8bdd4865092200,-0x45778780fe76ed02c3bdc966afcb0,-0xa4ac61a8137e803a953f7945e010,-0x130de47d4ad3b3251c16b7dac598,-0x1be7133f16bbd6bb3569d3113a8,-0x20848e472fa3f0d74a3bd872bb,-0x1e2c57ad881a658198b854501,-0x162d38494e4d416fb6ea25f4,-0xcc28349fd4fe78e474882b,-0x5a167cdbbe961c1a9c0f0,-0x1d76f592788b90ef0ed7,-0x6bca0531205cd61d20,-0xf662f311cf6051c5,-0x10950be36589979]
def m13 : List ℤ := raw_ints% [0x0,-0x434699b09a51129fd848d94b4bbc4000000000000,0x5bf3484ef8af4e2d4999e2f5d860372c3783994900,-0x3c3ca97f961b3a788e3fa4da9b627762c565c4786c0,0x192d5ba38bb46eb57caa6eb3f1855fd37110a0ec92c0,-0x78a33a0c9f9bb32c16c045921b6378a696ffa1e77270,0x1b8ec1051f8ebdc047cd35134439a45dd442216a0cd70,-0x4fdd0567f3d687bdf41ab317258fe28391e9e57a17d40,0xbc55bd40f2e94490ff92da83666b5bf7da32fc1415f40,-0x17006045832faa440bebad9a450a9e21ebe3bb6b1bf11c,0x25bbdca7f02fae8373967c42e6f5c85e68b61ddcc58cdc,-0x347664b11456c9e9144101ee64e56831c2d1329bcaaa20,0x3e3d20833136277ecd7b8b45fbe7a7f90fc9f4ffdc4fa0,-0x3f4d09500572ef0c5077c021a9b8f282a6cad1f0403080,0x375be14c32f3bc5b06bbe1d9c9b0a19f60862191ac4e00,-0x29b0b4bf11611aff875a7e6421e4d044adea8bad26ec60,0x1b0a20aae8077b20a5394ed91bf09a8feafdaefc1369e0,-0xf15ec1b7ff4ab47e77c1d4563155b92691e8ccff37b87,0x738bf2fef558dc0d7ff563f176a25bb5f1b04c80df777,-0x2f4705b1fd9aa793ac97fbd03f0f0042db811317d22d8,0x1071e14e4c17dfc1c8254f5efb1ec08747b6aa0532738,-0x4d40d3dbdc3cf21f95af98416b7577c90a8e522a17d4,0x12f8c9592f129b60a352a094c171e774fdac1ec9c174,-0x3da22c272f5ecc6d20473708483fedc20434f2889c8,0xa323b39df98e04706760319e00277a4a268a3660a8,-0x1595a8d351c6aad4b81ccfb7910c3055bc46e74a26,0x23af234857cd895f2f18b4e9804cd6c7ebf029a66,-0x2cab270ad3e744e4f73a5bc3d11c5a62e45d2dc8,0x28a31aa8e0b4e7837f0625560562b9041edf768,-0x1968efb875ea579d3b3afb4e1e04465b798de4,0xa18093a4a66973f13defc73b1edff6eb6bc4,-0x24463dd3d3b2794a54ece3fd29851350d98,0x3d3f0cd6f76d0cd17e16635f46cbd57b8,-0x22e4e8a2a50b65e6fdf883001267e0f,0x326f8dc39904e932093a9936cd1f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 18 56 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 56 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 42 indices rho q13 m13 13 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 42 indices rho q13 m13 13 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r14 : List ℤ := raw_ints% [0x306a204f08e9e68320ca6dc3d0ac0000,0x3f1640227740c62a120e591f553cc000,0x26628e210db690409c0b658d5705f000,0xe7ce295d6e4046ae352a0140dcb8d00,0x3ccdc4c15a85740237cae1678387500,0xbc4312694a7cefed0933ef918e81f0,0x1bd70cf4296e8a68c85815b7216960,0x336eff853e55a80d1675a9701af28,0x4b243c294eba9bbacef2d59e3260,0x5756f5d9bb77b0eecf66cb4d5e7,0x50cd5556140efe67c852a119ce,0x3b303b0b83a9b90ca63e90703,0x21ecdc5400eb6a0ef64d6948,0xee793a14cbdee220cfd36f,0x4d9a5c458e62882f6f646,0x11a398bc68228d81acf5,0x280abc0adf990d5264,0x2ac40c3b6b2ef11a]
def m14 : List ℤ := raw_ints% [0x0,0x64e9e688e7799befc46d45f0f19a60000000000000,-0x8894967fd394ce590f33fa79143ee07f8fcd2c58f00,0x5890c4f49d66b5e0670776b5e8a4f94bb40dca6d1b40,-0x24a0287df330006f0ddefe67bf35cb5aa2f0ea4ed2f40,0xad8dad54017838a582ccb330be9cca2f49352d24c4810,-0x272ff7833e35430d3268805ff0fc63deff03a4eb407510,0x7031ae3a607c6f748844823bd9ba1033390e2023f940c0,-0x10539ee5a22173ec9f2704a0a08ca8cf5358426fd628ec0,0x1f7acbf7e42d5444e9e3b385fc4f885bc2abb88cb01d984,-0x32ebbe2be50938eea179f23a388a238f4670e5b9b98a7c4,0x45c1709539ee2df9a12df3a40e9cb2e101c80d59d4434e0,-0x5178927cdf02f250e2a26033b980abdbcb805fbaa01d360,0x5180dfaf1ecc1b00caa0a1e531e077a12eb0492dfbe6a80,-0x460a74a9a51910f24f03141e548671717c05a0730180100,0x33c69df45f7227dac0352e273314e43d685c288a40290a0,-0x20ec5474b0cfd99ceccf3b8416a64cb010eee9b7ff3f720,0x11fc05391e50388de5cb089c93ecb5a09925e29842d05e1,-0x86ac1475db84cc2467fffd2056fbf1d1c93773e0eaa471,0x35c830ea293099248939a771f40fd45bd721d63c044768,-0x12397f2f46e93a8f885113200247a411bbf30133bc2408,0x5339faba7b76f373b434f0f2a794b4fdadda36e03e70c,-0x13d1fc7c74ea9ef89034f2c29707f036e60d620d4cc6c,0x3e4414b892b6e3aed07757e571187d2db35e151282f8,-0x9edba1efcfeb06d5bf6443c26d372388119b4f3a918,0x142e73154660873e75f20682c6adef4bef2512135ea,-0x1fe46ba88e36625c727294f3f69aa7210ab9a5bbaa,0x25f4dd5f0f7973ab68565cde6cab65b739d7f6af8,-0x209ebf3f38ad702962bbaae75ae5ada8ff3fb058,0x131e67d53e289d970e6c302861c9b0463843f7c,-0x70d3921d06118ee7324115781170639e6969c,0x174232398eebf03a24440fa84894d36682a8,-0x2389f3bff6dc01c33f21b9e37dd3f4d388,0x1203c266c99d2309d066bb68f3c03819,-0x16af646393b98581140f60220b689]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 18 58 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 58 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 42 indices rho q14 m14 14 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 42 indices rho q14 m14 14 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r15 : List ℤ := raw_ints% [-0x7cdcaa27c8ee1150e9e0cc6e023380000,-0xa2892cf6149b15c066de4ac9d52d38000,-0x62c86d784b55023ce8cece3b23a2e2000,-0x253ce3914aa864087472bae758ab9d200,-0x9c11a3e97b6104e1248ab98ebb748f00,-0x1e27df7e319fc31ea48ddc729e809c60,-0x473b18890bff708273b7ce9a1a690b0,-0x8359fdb9030491c7194b6d0be3bbd0,-0xbf7fc067655baf47af7abf37a9588,-0xde1205a782e8cca98d8ff4ae85d6,-0xccea0aec208958fb5a20f9a8fd3,-0x95a9be04c46e5f51b763ff93da,-0x557fd272d11b39300289553d5,-0x256bf8553664d1d43029d67c,-0xc20102cc5eed32c11b46ed,-0x2be0dcd49bc7460fb2832,-0x6308ba46362264d33b3,-0x690ed49e2371b70f2]
def m15 : List ℤ := raw_ints% [0x0,-0x975ed9cd5b3669e7a6a3e8e96a67900000000000000,0xcaefe62d354b1d93f5f4de6190e93c7f5eb6efbfd900,-0x824c91083bdeea40a4b79d852795e244103ba2fcd72c0,0x355494a3fa876aeae7acbcf12a020c90ec93155a6b3ec0,-0xf9feb9a2b9fb299ae6e70703d74600088b34984d6f7970,0x37d00803fb9cc5b71f67d2ab57de57cfb14496a7c368470,-0x9de8b5aca461d4bab88cabf583a7359f1c3a433426c5140,0x16b1e4cf106cc3a961fa1d3007143e4aa9d58652a9b65340,-0x2b3081d98503c7239bed04be6e8649604ba72a1092671adc,0x44e7fc5ec44735dfbb2da654a5a3ae4afa4c16333bc2d29c,-0x5d07f0984c94f8ee6ed75026fceba42ba08722c5b829f420,0x6affacc67a238fe02a435355213dcbe93097db599a7371a0,-0x695053ff585a2b5dec61f5e9454bb8dc565654f396352280,0x58f40a2ab384eb742173abdc6f567e52a1f65248c3b5b800,-0x408f49509c1afaa95cdb134e61edeb5633d1757a3798ea60,0x2841895bbba72cefe71ec4dc3c2ec52c69f99351832cffe0,-0x1588ccd89398558de658406cb3b2ae118ee706db07b6d677,0x9dac96556999cb11834d3becee882f70132e946c588d967,-0x3d77062449e15cc50f0fd647294f57878e71a2aa993e458,0x144ab36bd2ea86ec6e0ccd827078890bd645a3c6732beb8,-0x5a157111d23aa1fce4afd890466830f8c62c31ed4e8f14,0x14cd9ef51cff350f32d36abc416aa154dfa19bd4d302b4,-0x3f30f2faaa24144150ed02ffbc510d4018d99c0e4c248,0x9b5d137590d701ebfbc6f7b0167292e09af90e41d728,-0x12f2528faa393d8f63d1a9aae7ec60b7f24582173386,0x1c9bea8f40428f2fbe1a20210244bcf784d9be8e7c6,-0x205b6b2d13ea221f2126c06267e4e0ba0883b38e48,0x1a40f9341dfa2b531f45c994856034551206a21e8,-0xe69d2efd14237c3790ee4ddc1c3ad0002aa2424,0x4eeacb0fa71304ea05e967d1bc9b5c19491004,-0xeeba1336337383c08de3c60ef84822bb9318,0x149eb5a87dd8749ac1269d3db00f9c3af38,-0x94bed5d5938f8ec85d9f4683ff74217f,0xa33131cde37d3e0a219f0f5c9d98f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 18 60 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 60 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 42 indices rho q15 m15 15 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 42 indices rho q15 m15 15 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r16 : List ℤ := raw_ints% [0x132bbf9d0974493fc4edb96a29489580000,0x18ee9b764230c4bc5bb60f4e55068f98000,0xf2324d46abefa6df5077c77e2ef977e000,0x5b32946ef74af20d6ce2a70269e0cfda00,0x17dbfe5e64794b52d2e3003639260f5a00,0x49a95a4965601a9e8ea989c32c487d8e0,0xadbbef7d5d0365a37c8f6c790c970fc0,0x13fd64aadea2046f2c89217e3f709dc0,0x1d16efd1874ffcb032c595f4448c420,0x21aa0bfd32ff5ed218330cc4466f96,0x1efe07226afca71f18cf35c83b13c,0x1693e4ff7df9f30d88811894c035,0xcdc65d80b7e636626fb0a2529e,0x59c55247de560201bc1fa0f5f,0x1cfab9f896ac786dd5fa4bf0,0x686ceeb15e1442e5e2d8ab,0xea8aa9b51308253f6ed6,0xf766f72227e89ae40b]
def m16 : List ℤ := raw_ints% [0x0,0xe30e46b408d19edb79f5dd5e1f9b5800000000000000,-0x12da04fa12c53c9f299b7392986058da31826f8a3c7f00,0xbfd127c95115b9c9f5ca4b9f62193f445bc4784b754f40,-0x4db9e87858cfb6abfb262cd918628d3fa5ec7b81eeea340,0x1688cc91288a77f07de6c2f322211b9707cf1f94493ce910,-0x4f9d0c46c589864a0c9d26ed53be107d97e384d0fab3e610,0xdea8f451c8e6b2f856ec094d286528e8ae11cb17b36e4cc0,-0x1f9d4e760ec965b0f71ca165a972f61c5db8af20e75e07ac0,0x3b661a5c5e2aaa6c6f4b2d5e777185816e659136c1dc619c4,-0x5d7f1ca0312e89fbf77bdbff1e614790bc5b57541c76b6c04,0x7c715a615a42d86c2a920f3cd087107818e46d69d7e67dae0,-0x8cfb38d1c1ab7dc5999fcb4469a29be6ffe49263bc4c1e160,0x888e491c8e4706084077581fbd6c6b731f888e1f6eb9fa880,-0x7164d2f3f5b300b1c77c1aeda0a9bbb4b308d6a3415f20700,0x50d14feb056d96ee4be23201628f65a3c0d0e9e2091e9e2a0,-0x316cff1c501ff19cc65a4efd73789957d17dac76aa051f120,0x19e562088c4a88c31e2ecc8fb28b258c82f7583d1a4aeb971,-0xb96cbc56f2f912df62d102a899d3df9443d3c206321af901,0x469078a203fa5c7c16ff21e3e53fa53656585fd17c6c69e8,-0x16b28416b6ef1ea95bb9d3cd3f3d873b5e6c073a17d88088,0x61f4684d3e569aae5c5cd145f38741247fad3a75b007dcc,-0x15ef28fde3b988328b6df2d80d2722bdaeacc0c7d06892c,0x406a05f8eb2929ba4a4697fe40f5088ce8413e0417d678,-0x9896ab422fe0f8b782eb2108b71cd962bda1dea2c8e98,0x11db7c07b12562ac8aa0555a7f8dc490d1ae31b49dd8a,-0x19c14e8d2462df4eaa5830713aa1184715ebd29d5f4a,0x1bab1ce67da530820776f5e7949bbf77fc9ecab5678,-0x152eb34d0256f336a73f2431131a183a8f0383c1d8,0xae2be02e2e9af0b8feee5b75e7619a45c7661f3c,-0x37427229177b11e5a2861a2072f12df80bbb85c,0x9934fb0f5718c5b53bd664d554d4f907cc128,-0xbf65cfa4d7d990ba9d5b61922052c35f008,0x4cbadc36bc9d6c6a843f11fe187b96f29,-0x49589dfc6f617b4d6e31043932dc99]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 18 62 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 62 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 42 indices rho q16 m16 16 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 42 indices rho q16 m16 16 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r17 : List ℤ := raw_ints% [-0x2d2551231d3104fe4609398379efed840000,-0x3aa9c8dd9d6cdda4dd5b8c1d2e78ddaa4000,-0x239577e74a14ea44867edb5cd4925ed59000,-0xd62a011340f861c2e0d9e939e5fcaee3700,-0x37f7b28c5fb85c8d310b0d83f7f5215a800,-0xac93dfc4964171bbabdfd0fc4e2c7547d0,-0x1967b31f7956a64a78b17590f10f5de350,-0x2eb324e25e6e4d03122cfb454ba33c0e8,-0x43d8a161fb0b9a6da7cbf1c42f58e528,-0x4e5f38bb2619e28456752b7306a25ed,-0x4801317597d56a3cf743ac50ebf7a5,-0x3455ff2fe7059baeae70de6b4e550,-0x1dbc81d4c62051f5913f557442ff,-0xcef8878c269471d03f0e3a3870,-0x42991deb9e87ecdcf963e2003,-0xef1ad3f21293725cf04d6f4,-0x216cac59e5f05407d55861,-0x23168da126765b8f1927]
def m17 : List ℤ := raw_ints% [0x0,-0x154956a0e0d3a6e4936f0cc0d2f6904000000000000000,0x1c071a197f74c2971993238679939659c72b8056b6f6900,-0x11a8cd900696e2f2ec8f5f931bc8f6c2c9202b22c78a1ec0,0x716271b5fecd4539e855e34b24d0274bdd5b114a38acaac0,-0x2089f9477aba176d94af317bd382c695c7f037cb8fd25f070,0x71bc2a9ec736f395b8d751b275595ca8a2cabd03e7f05ab70,-0x13a871b027a02189339da9adfb27e152daf0556c250e306540,0x2c21bd39131c607a380dea1037ff711d07538d70ac98468740,-0x51e2ce40b0cbf636736f90aa619f7707b8e37654b58c9b609c,0x7f330928838a1adcc20d7a8d90f434ee51a700752389f6f45c,-0xa6f2a4cf9530a8b222bb51115f965e8f0c2a50dd66687ade20,0xba59380d8097ad059331f803301482328e5acec70a7139b3a0,-0xb1ac7347693bb0ccabf6379ccf5f4e9bb3463bae028891b480,0x91143a483a170e2cb889dbe6c4971ba0eeb1db549d50fa4200,-0x658fc866ba3e6453f5551748f57cea373aeafca794a5bec860,0x3cee4bacefe41031191d937099458f3a5611dda26c6ff3f5e0,-0x1f45cedcc2c76f51361b3a42be8ed70ccf73a9cf0ababa7067,0xdb0262ea51ab1e68f715689455c25aebc13ca2bbd3c136a57,-0x515f0dd93ba983b9477333b58576dc6815172a3fde1e1bdd8,0x1980935aee08cdc9c8a6f8189f31540dc7d83e67b1570ce38,-0x6afe0ff2d1db2fb6c1ccb5d5ce09a0d0beafd4bf91a4ba54,0x173ab44901c7465e27c515bda3c58b24d01854ab638097f4,-0x41f188c0493c71195e7e812dc59e0a4422b20dbccbc82c8,0x967a232a4ebb25c70b53da872e6d81aa3e2763b4ceb5a8,-0x10e50d3906730b25e5133fcd2e08871f03cd1bf9f112e6,0x1743cf6fb00ee80214e419a91e1dcda9043cef3f76b26,-0x17ba67118cd610e6e0f3b81d6ed55c49359495c9f6c8,0x112168e5aceb0c74718a58935d1415edfe24bb0f468,-0x83c34d6e476f5003817dffbec6b1c784cedb8de64,0x26bb6104ce31d2747d78ad8846c7105146a3b844,-0x625b364959607223f05d2e3bbf1f2f69907098,0x6f04d9dfb98e9f386e1c67e84e83119b7eb8,-0x2790a358ff3588f110524cd95309120bef,0x20f40f43837c9915c1329986818bcff]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 18 64 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 64 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 42 indices rho q17 m17 17 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 42 indices rho q17 m17 17 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r18 : List ℤ := raw_ints% [0x667212bb5348847ab5ab4b77ebb1ceed40000,0x85045808ad02acb1bc84365553be4d45b4000,0x509dfad2ff4e9abc8c9903179f432c6de1000,0x1e4c03dc167ec24e587fa8d4cdd64ec679300,0x7e8d3363e4f048edefd975486037132ef300,0x185ca719f3d47223d7662d9b8ed021c13a10,0x394f895cbc56d3799cd43cc09e69e8c0c20,0x6934fae024c78a14a7db6b02fedc3ad878,0x989e8c696d78a235b00f4dfdae81c4a20,0xb001eb7c684b10e3fcd350a2b8025ba9,0xa169f15ab455763f016661ef61cda2a,0x7515d2f47297c9d41d0084a1b63ad7,0x426048adb4ee3030d5c63a260d4f4,0x1ccd40acf780ca89ca3cedc987a7,0x93dd44560447e37127ff5fdc1a,0x2112e3019964911d0da81b7b1,0x49b4fc2fd691376389ae808,0x4d0e800bafaa9c11f1120]
def m18 : List ℤ := raw_ints% [0x0,0x1fee01f1513d7a56dd2693213c71d860000000000000000,-0x29aec1efadedb0e4a9690726ec91ca113e4e887ca7026f00,0x1a072a153f7d47afa3641de2ad7c77a6281453f57ed68c340,-0xa58c62db60629ecd76907543145a53e60129590de616f5740,0x2f0a6ef99894253b56f142153e02590f4af926c3f454999a10,-0xa2b85a3c4bb8f0d497d6586ee96aee4d5e5d006206abd06710,0x1bd15385d23ed313dff7740acef50ff200e90d96ebf7d8818c0,-0x3dbb3e9bc4a73b0da23894afbcbbc7a7ac8995524108f1126c0,0x7126389f87c643a834f65220355d16cc916cf578056e5e7de04,-0xad807ae122e7d075dacc4bfff1df8810c8a4a5ec907ce97f444,0xe09d2f92146861b655121378a79eaaa165dcef1f822de14e0e0,-0xf715af76d1d8dd60c675eacd50f8d021557d153183cd691cf60,0xe7f37bdfc16d9a1a8001a777c3034675a813127734923f74680,-0xba4908972be9602882ff4b481b8a1153403a17ed896dc22ed00,0x801d9c75ffa61b4e949b7c2d14e925bbd0a3f6521ee358254a0,-0x4b69e458d3ee536df6dda0f894de705ebbce2679a6787ab8b20,0x25ec1bc370b44914e7f14559c4f0731044cb7d1eb6048821601,-0x103c83d9828f657a7743e17f019591c282da0f919d86c100691,0x5e3e1a37712d4143b3fab734ecb30b98e93bcf91ebf48bb468,-0x1cc7ae6faef6e09480f78d38ca4773ec319af967143ad5a508,0x7560b06e502073200d8efadbd33b55ce8d6197554eb02408c,-0x18b511b3c4629c190a67558a15a598bee6498751adc69d1ec,0x43cab322852ceabdd0bdf564e3fa0a78c737b0f90efe61f8,-0x94fbdad354008340694fdc8edb8423d73fddf190d0dcc18,0x100ae454dc8ece241805f6014f176c18b2e07b3b87f9f2a,-0x1515824011e66dbb0632acd66cbb9f69a0d7a91539dcea,0x1467c38793b5b23206da8a6f4eeee38508c74c347f9f8,-0xde24a5188ddb2a081797e46397b1b3dfef9f08ceb58,0x63d570d09638ae7dbd8317340830b02f0148983afc,-0x1b2bde55a696848cc131960e22fcd4c567827361c,0x3f28fc1c307bde8be7cd0f4571e488d52e4e7a8,-0x406249bc2afa2628073e065163d7be110d488,0x1464a564f2adf60ed1e2f3f002a13990739,-0xeccdfec565b5c01107d05ed034553a9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 18 66 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 66 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 42 indices rho q18 m18 18 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 42 indices rho q18 m18 18 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x4d0e800bafaa9c11f1120,-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r19 : List ℤ := raw_ints% [-0xe0fad4c5a1e4a6564e2c6340b72bd6ad800000,-0x123e93530ae826cef86d682110f003631c40000,-0xb0c7e065b40fe8aed7cad977cd9a0ffebac000,-0x42615d1960f014b6113ad53d7768e1344b9000,-0x1150459aa012550e89b41d190989dbefb72d00,-0x3545fc903049d0ba98be672ac1143b1866b00,-0x7d2f4ec02c70ef2a0112c57bc784f27ea7f0,-0xe58670760ced0a3781cc07cd93f168ccae0,-0x14c840f86e03a4ed7d975048f1d5eb09688,-0x17ee7ced174c84a731fe10509ae38e95c0,-0x15e9575767e55b758392895efdab83777,-0xfdd83fefc304764ed4458425ed66e56,-0x8f9dfbe150c4b1b2e9f162eab464a9,-0x3e2dcd2788e03fbab014a417d324c,-0x13e6bfba4fcc0a8c502a799b6b19,-0x47062feb0de6b0d83c29487566,-0x9dc854ee9889ac0e18e500cf,-0xa45d15ce5e1b8b4040c1d8]
def m19 : List ℤ := raw_ints% [0x0,-0x2fe502e9f9dc37824bb9dcb1daaac4900000000000000000,0x3e02096914167409e27f406860c605611190e43330137f900,-0x26626dc4b6eff1bdcf8b2f2782c348e3058f96dfb654698ac0,0xf1eb7ef7e561288651bf4fd42e9909598a28824219d15cd6c0,-0x441586b7bbbe8f8102376046dd0ab28666e0f1d6182ebd1d770,0xe9236476814323bed167ca419b30af749b215bf7e032d054270,-0x276ea7e0ad6636f272b1a361eef04e71ecab5043a9e73621b940,0x5685e4f5e6adbda0fdf92c5cee504eee52796030ec662845fb40,-0x9cb4aa9b342d91c6d7cbd4dc6383740e75004188da6807ba825c,0xed437a93ae3356cce86dcf33f812e7ec2df42f300e70c0bfb21c,-0x12f0cc57171107318c1989ba4eec0411dbb275416324decc76820,0x1489f21d038b3e6967084d8dac0142d1bceabbe21ae1d3c1115a0,-0x12fcfaa2c706bfbee683d30935811ac9ed7dd80eb29ddcde5e680,0xf00a2ad3dc6826e2c6f30ede03e8a810f630471c0c495181ec00,-0xa2374f273a8b204dd05e0fc5fca70bd23f3fa4125332b59e8660,0x5db457c1b2b133cba0c1aaefcabf25c25a97cb3162d018464be0,-0x2e2c4c037c75445df6c79caf0fc07a15ce0b01019a4b25043957,0x13570021d50c5f85aacb93b876ce9203cae81680f84acb2a9a47,-0x6d9dcfcefe60e2a20b46bbe9b9f7a31df5fcb1fa46d67d02f58,0x209e7d557470bbcfa1b1e82d8cb745241ddfcf701e83e6cd5b8,-0x8152ffed3d81f11d24b9ef96ab725082aab16b93f7a32dd994,0x1a63e3540713f6f0bb5fad5862f6feebda00a8b3cd6c9dc134,-0x45f9bfa912e4ed5e37c1080fb43d01505021992f581f84b48,0x94127bfbc21c6f5b30d463c72012b00308d06f20f3437c28,-0xf497f2bb82c54c1967710487c4ede42114be6c507aa4846,0x132ad06fdb75a48bee67b0485baf1b179be56f512278486,-0x119808b1f25afdbb0ed4fae67a4ba4ca8d142666f8e748,0xb4693dde8afd3b7290b93d1e2743c16d8d9739c4eee8,-0x4bbfac22c3cd6b9483656f9cd3449d55f361b03fca4,0x13137eb4fc3351b3cc9592395ffa122df9afe7a484,-0x28912b725099e5ab39007611faaac615b9e12618,0x2554b46253a1241cbbb6695924591b0e244638,-0xa81d6bdc5afd913c02852c3eff23fa4ad5f,0x6a51cdd406b169d339e4469621a0e76f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 18 68 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 68 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 42 indices rho q19 m19 19 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 42 indices rho q19 m19 19 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0xa45d15ce5e1b8b4040c1d8,0x4d0e800bafaa9c11f1120,-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r20 : List ℤ := raw_ints% [0x1dfe31e661cd17fed68dc59d070103157e200000,0x26e3fc4c302b3639ffcd4580837e25e7c8b20000,0x17890eaff58da66b194c46c2110201e6a57c8000,0x8d4a1468b53095d4a3a05c2b973031c0b0d7800,0x24d20a09832138450b6e550cae372cefc498000,0x7130deeb25a08f82938a8613d0111e07970980,0x109b6981d08a8f05179e162808d1724e854e80,0x1e6a48b59b664077302d6ab215d7d88975150,0x2c025d7d6bd6a59d25d0f3c7299f4954e060,0x329c56683f1deb25667ac8d20cec0240460,0x2e45379fc28bdc0462f1371a90447b9d98,0x2172c2162a667d815b3604c42d9cdb2e9,0x12e3d5162ef35fde03598c019af0554a,0x8297fef57609b4f48798c532fe12c7,0x29b4bca5e43f876ea904fe04021c4,0x9478f2bc2328b7a4503bb91ee07,0x148ebdcf6280e00a9cebb988fa,0x15591dd5500658b4edae4199]
def m20 : List ℤ := raw_ints% [0x0,0x47d7845ef6ca53437196cb0ac80026d800000000000000000,-0x5c452977dbf96f6ffc0b55c6ae2b5417f5404809951c075f00,0x38a3901eb51df742a8230e91347de0ab25fbaa61f41957b7740,-0x161d26de5deed01e3ff7bec69e79a29f3eaf81dc98fa26e34b40,0x62a6eae70af03d5020e80e1b38a1d4a67ba12e917060ea435b10,-0x14e8028f704085e9c226c8e45a0a00d0f8997c53907bdc7c6f810,0x37fd935ca3984b3b0ac2ecc3b533b208a64a2f049a2adaef2a4c0,-0x79825fa9ee2dc4b5cf5d9c38bc9cea45bb0bbcce68f88108092c0,0xd983b5f297a05d8b84c80b8b35d082e11f6c5e997e813b96f6644,-0x14545123b4c57b05ae963b7af48c68b793268928b494b1e86a8084,0x19a0146976070f93e453de9f6cd027559359b4370d27c95c1146e0,-0x1b6618785d9fd22366578e4c6281f38e5257437833f1b5519f9d60,0x18f39cad569f931a539f9cc5a10a93f53ea9cb391fc590c02d4480,-0x13660aff9f5cdc2e6f5b42783723dff24f1bc8cb334478abdab300,0xce256d76cc8aeabcf0a9b07c7d4f4fb58627065779c794e55e6a0,-0x74e11ac1f21267aa176e1875d9a2064d6c2c0ce1e33d738f2c520,0x38718b7a066033dd76159a4474e9107e2ff4b889bfd199607ab91,-0x17219a23eebe02afafb24af646dd87bd5d5bfa569aad8d25b5d21,0x800856c5a5a0aaaa44e8b4af3cfeaf8444e6f6db56b637eca6e8,-0x25205b3fcffb8152fa1073a0a3c3363fa598a7be317712581188,0x8f15bd7d7b3a9bdeccf8b8ea29acdf6a3f159d3099693a1ef4c,-0x1c4dbb8cbaaed8d7645bb5df2247f31f2302cf0c9b8907d66ac,0x4883f68b6075d52c5c83a23b956411e0fcad339ab81e29a578,-0x93b6b00b035864c756f0b6501eee008514dcc09eafc2ce198,0xe9de0729ffe6f55977ad39f695cbfc0d3f1cd6f7779a1aca,-0x117a0a89ab18b3a0f85a0399b491ed35d28a0f56852ed48a,0xf351e164997600ff6b83ab2df808c35f82988c9058d578,-0x92cc8c53d89b008d19cfe3863d98f96529ba727a4acd8,0x398c77ba0d62e7cf37e735c286c03b3143a3be2e52bc,-0xd66e5f1f310a941dfc856f047bbb8c60b62d3ecfdc,0x1a0f4d59f93d552c2408eb9b619158f9c01d57628,-0x15a3e2b04184a00b6314f853b569171d93a0108,0x56959687539bc2fefe27499cc4f71ed11049,-0x2fb8154e648d6eb79a59c1e6b5a892bb9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 18 70 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 70 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 42 indices rho q20 m20 20 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 42 indices rho q20 m20 20 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x15591dd5500658b4edae4199,-0xa45d15ce5e1b8b4040c1d8,0x4d0e800bafaa9c11f1120,-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r21 : List ℤ := raw_ints% [-0x3e545368b483184643fed27313673c4fa922c0000,-0x50c58894ce1c8955e0eb53ce09cde122a9290c000,-0x30d9439ad030a897e0f588fdecc6a253bbf09b000,-0x1250b3dbbdbb4ef8e0445f8377a4fa271cd841d00,-0x4c4f1bd956277767b1b603b0302d11dc5445de00,-0xea62aba03e7d798da08aab9ae78838bcdd691f0,-0x225b4d7ae62ca084619bc9f5d4da27f04f82e90,-0x3edbf3b352c5e0eb7fe804c8d5c3ad5ffb5fb8,-0x5ada7e07cca7786889e06e609281327709da8,-0x685adc02763ec64e3c58a3e179c86016ca0f,-0x5f474aef1295aa9e04fa628ca09a8cca249,-0x44c6519989caa5bc7d3af7972951cc32ec,-0x26c721e0f7ee59ae9db502513be66ffd3,-0x10b9b9017fb42c145ddfb3f272b51390,-0x554b0baecaaa471443ea695cc6c12f,-0x12ef927d8c0c1bbd3bd2fc90fdf88,-0x29d8c77acd83dcaeabb3072f5fd,-0x2b561b417b60aa2921d2ff4c5]
def m21 : List ℤ := raw_ints% [0x0,-0x6bc3468e722f7ce52a6230902c003a44000000000000000000,0x8956c58582dc4d23a3fee9168ef44b6d128c678dc6584a98900,-0x539ecf3cb6f3222f42b8b94a7a9d06113c2dfefd50246e17b6c0,0x205e95b7a327a36ba66e4f129acb8e56d05f904b9f6b0ace7c2c0,-0x8f19f3eb0b6f4b091ad9c451518176cfaa50fe468eb8d56aa2e70,0x1e097d10064f3ee5eec77f2939479b9cd70a67eb7f1445559c4970,-0x4fa214f3201f55a000410e640cfa5bac7acf1cbeb177ba29b44d40,0xaaf874861a560faa3637b4faf9221131d9ebc544b5c376c348af40,-0x12e94c4082b129dfe748089af08d115b674366aa5561e647c22401c,0x1bf0366f4e9f258eea836d71bc071098291ab45dad5ae459396cbdc,-0x22c35b451f53f077ff00faf4ef9b08a3bce46063c9026353d399220,0x24a86e57f1c02986d114d13491a06e8e5dda6a1ce28423b127b97a0,-0x20e470c1f9185a02d3346daad30060493968ddde9ff97e5b471b880,0x192b142184994c719a287eff3a78d8a6efe9b70a09208f3bc84b600,-0x106eaadbc35b36abbee28108f0c714b66d272e0fe28c5bff85e2460,0x925616ebc3035c45c0d70bad0ee9d014ebbf0dfc6e72f518a201e0,-0x4544ecd40be33428fc2f12f6fd0408e73a77e3f8aef6a8ad092147,0x1bc710d8325d01a42339f9557c9f499ae9ebc6770e006c5f2a5937,-0x962836dec024ff568219311e916b032679343b1241a5ccc20b8d8,0x2a6e618d3b0b093580c886cd30e3800e9bf11bb17b7a8ea3e5538,-0x9ef5a15d0eef35a87b63743ebcfabe11fbfaa4caff1102a72cd4,0x1e7a41fc0778b3438a72859801193ec4ab114e58e7c355d1be74,-0x4b6fbda1a7877577334b78b8531329b10d3489777ba05e89bc8,0x93e2e3c7fc0fa373f64a788771d18f2e5bd34cf878d1eeaaa8,-0xe0579eacdfbbd7430dbd51050f02040ceeff75ced615633a6,0xffb107faadc0b8912d06e402641c138144baaada001093e6,-0xd2cf8942f3701d8f04cd70b9888617fac2f50b092e0dfc8,0x77a98584decf4d63a939ec9f637162e9559e4cc4909168,-0x2bc5f95b5fca8dbb3263103ee967bf2bae3baef15bee4,0x96bd37aa930badc0c7db458c71f3c1edbe3de8d14c4,-0x10be00063fe26ed298cf235acb44fbf99061733398,0xc8a9dcdaaeeb5b356bc7bf0535e452ffef585b8,-0x2c9393dabfd63039e7af5eac2988b3d9f75cf,0x156922cbcbd629d21d6f3ce7287fbec8df]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 18 72 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 72 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 42 indices rho q21 m21 21 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 42 indices rho q21 m21 21 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x2b561b417b60aa2921d2ff4c5,0x15591dd5500658b4edae4199,-0xa45d15ce5e1b8b4040c1d8,0x4d0e800bafaa9c11f1120,-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r22 : List ℤ := raw_ints% [0x7e871b87c88cfa7e2cb431d4a2c99a4928ec3c0000,0xa3dffbcb0343db3366215841e89b7e6917fecdc000,0x630c504174d76951f0ce9c36a290ae2609eff73000,0x251cd795cf8c164105ad50f4c3e54ab97b8d1e4900,0x9a8453e26b67d710453270dc5e434aac769774100,0x1da3c27768a90c5590f1c3b0f0d80c17031a10b30,0x4574951fdff26e59ab8a520117f954a6376946e0,0x7ef56da409991c5e6923ca9cbea794646bbaa48,0xb7507d2d95abedee08239dc5c3a7515b4ec2e0,0xd252d6438f8a6a2b1642b6ba6faeebaad69fb,0xbfcc48572561c29951f23970cfd4e0924c86,0x8a42e4ce1b457dc146ddc5d0f632867746b,0x4dd7e35058911e2c794c4c2e88341a60a0,0x21855eeb4036828f1fce214a9950d933f,0xaaa3b8b36960230ab49fdd14c6d6fee,0x25cf130a11f0719046cb3e390ccfad,0x535f3ca3c568c929749b836e34ac,0x56210398ff27cc42829ed0ccb6]
def m22 : List ℤ := raw_ints% [0x0,0xa1a4e9d5ab473b57bf9348d8420057660000000000000000000,-0xcc79c2cdbe154a4f3a445bbddc60303cbda9d4dbcd1eeb3b4f00,0x7b855e49d146434a9c69179fbe424d5f17b1ee62d4ec5e4216b40,-0x2f6b5667889871064c3ead29bb09afb2b13efd99563b5658fe7f40,0xcfcd0c6d5a7da2fac94ca874f95a86865aa888d5be4160e82b2c10,-0x2b36b3c24e4949b4b7513321d8731531666809753a0c95ea0d89910,0x71711a009bd4a661fee05306cb65f61171b7067fabb01d95e19f0c0,-0xf1048e8824d4136b5d5faecdb040a341ffe75401a718e9bb97abec0,0x1a5d197b42bd1a25f0bb0feebe9f264ffa31d6ccac11086aafa8f284,-0x267ccc89f73d88d25c752efe5e1060d97a937b724642a33fd1b350c4,0x2f48db01a337b2b2bad2107cf52f12cd025b0de4888b77a476030ce0,-0x31302ba161aaf604a28d3783462c2bdbd6c0f94bfd58dcf370794b60,0x2b7eeaff101dbb9d9b62d872dc6cfc3eb83ab64a8e0b340a5539a280,-0x20c35ba05f5aa4652db05734c77d02b706c46e13dccedd30d4595900,0x15081d830a2497bd20d624491d6164627654c8c4680da21785ce98a0,-0xb7e5910c7cba20b24df84468ec28dc3508a94ba732c56d87d799f20,0x555636570d64ddb41cebf9170a3fd25c922fe240b18b285cdd90a21,-0x217d466504d1c1562c54a8cc1d041c412687a90f23b8042b8d78cb1,0xb0d06d7739696092d4b827dc9e6b4e31c1ee1bdcdebdf68101c168,-0x30b0b1b0c88fd65437201a0b198b33cc572d77e33e0003e88c4608,0xb14db4c74b97c8f2719c916fa665187d74557a20fb107391c4a0c,-0x20f25f413cc2999345495590ad4e87d4239a54180f6793744076c,0x4ec4ad6f6044f2c56ea8093f1a254d9dbceaf101d6fd44b520f8,-0x949316b9992bf4c0612a509c36628c3af4a4957ecf08af74f18,0xd7e1a75af9516a64106bb740b2008ddec801b7e7cab662f06a,-0xea70b0819b97d984da250ad313feeacdcf9c50e88e161e62a,0xb70cdf70d0939a7a4d94e28b5f1fd09608b00a3de75968f8,-0x61b42d06ddaa8c31879a049d4c313639b4145beacec8658,0x2154cee7f8ea1a68bf2ceef7d54dac313f33137430267c,-0x6a055857fa67b1f4f3ec6902146dc2ca16cea2ac459c,0xac1b6f25d7d309827450a370eb116143fefd2ceca8,-0x7443964aeec9bfc07b17da85f0276dce14edf588,0x16f0d6cf6222fe44579842d177e718a1ac9a59,-0x99a831be91b5b9cf92983411d48c7874c9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 18 74 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 74 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 42 indices rho q22 m22 22 19669684177686137322663936000 24=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 42 indices rho q22 m22 22 19669684177686137322663936000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_22
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<23) : intPolyRF (mz e)=rfPoly (C (19669684177686137322663936000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^e) := by
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
#print axioms moment_source_22
end
end CatalanCore.Li2.NVMod.FamilySource.U6C24
