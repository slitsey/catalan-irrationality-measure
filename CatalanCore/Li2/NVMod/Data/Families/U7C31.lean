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
namespace CatalanCore.Li2.NVMod.FamilySource.U7C31
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,7,31,size⟩
def bases : List ℕ := [1,2,3,4,5,6,7]
def indices : List ℕ := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def num : List ℤ := raw_ints% [0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def den : List ℤ := raw_ints% [0x1497b6140ecae2340d4c400000,0x1d89adfbdd7a99a8fd0a940000,0x1423eeb43e35575a6b088c0000,0x8b04cbe62174b5583ae653000,0x2a9b11d3a1656847066a1b400,0x9df9d627029b54226b8bc500,0x1cc46dfa035348c21b21f7c0,0x4390786cd3eb840d1b04ac0,0x8231c7f93b288d3158af70,0xd06813b033b2925c11830,0x11786929902340d019e74,0x13bf0c1712484a4812a4,0x12dec185613766fd431,0xf43992e07a2c0b928,0xa71104354435486e,0x6059f84a6e016cc,0x2e979a4c11caff,0x12bb9ebac7fe0,0x62fbd6a3c88,0x1a62f3077c,0x58934a7f,0xe13c48,0x197b6,0x1d4,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x1,-0x37,0xb,-0x3e9,0x8f,-0x8f,0x2f7b,-0xa16f,0xe28eb,-0x10d0971,0xb24bf,-0x7f5ad,0x192c265,-0x242f7713,0x200db3,-0x321567b,0x904903,-0x183d6b,0x217963,-0x1b94019,0x183ddd9]
def rhoDenominators : List ℤ := raw_ints% [0x73b3e4fdf500,0x11e2ebbf60,0x12802d40,0x375ba0,0x49cf80,0x9f60,0x3bc40,0xd20,0x1c0,0x1a94,0x1518,0x8dcc,0x3fcf0,0x141c,0x888,0x13fec,0x1aa900,0x1ba0,0x408c0,0x16b60,0xa180,0x34fe0,0x10b2b40,0xc007160]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-8) 0:ℚ)/(rhoDenominators.getD (m-8) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 8 32
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤31))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤31 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 32 omega8=padCoefficients 32 (omegaCoefficients 31 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 31 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 32 omega9=padCoefficients 32 (omegaCoefficients 31 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 31 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 32 omega10=padCoefficients 32 (omegaCoefficients 31 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 31 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 32 omega11=padCoefficients 32 (omegaCoefficients 31 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 31 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 32 omega12=padCoefficients 32 (omegaCoefficients 31 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 31 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 32 omega13=padCoefficients 32 (omegaCoefficients 31 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 31 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 32 omega14=padCoefficients 32 (omegaCoefficients 31 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 31 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 32 omega15=padCoefficients 32 (omegaCoefficients 31 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 31 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 32 omega16=padCoefficients 32 (omegaCoefficients 31 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 31 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 32 omega17=padCoefficients 32 (omegaCoefficients 31 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 31 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 32 omega18=padCoefficients 32 (omegaCoefficients 31 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 31 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 32 omega19=padCoefficients 32 (omegaCoefficients 31 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 31 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 32 omega20=padCoefficients 32 (omegaCoefficients 31 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 31 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 32 omega21=padCoefficients 32 (omegaCoefficients 31 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 31 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 32 omega22=padCoefficients 32 (omegaCoefficients 31 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 31 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 32 omega23=padCoefficients 32 (omegaCoefficients 31 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 31 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 32 omega24=padCoefficients 32 (omegaCoefficients 31 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 31 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 32 omega25=padCoefficients 32 (omegaCoefficients 31 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 31 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums26 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens26 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4]
def omega26 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums26 omegaDens26
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_26 : padCoefficients 32 omega26=padCoefficients 32 (omegaCoefficients 31 26) := by decide +kernel
theorem omega_spec_26 : coefficientsPoly omega26=omegaNumerator 31 26 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_26
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums27 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens27 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9]
def omega27 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums27 omegaDens27
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_27 : padCoefficients 32 omega27=padCoefficients 32 (omegaCoefficients 31 27) := by decide +kernel
theorem omega_spec_27 : coefficientsPoly omega27=omegaNumerator 31 27 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_27
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums28 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens28 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310]
def omega28 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums28 omegaDens28
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_28 : padCoefficients 32 omega28=padCoefficients 32 (omegaCoefficients 31 28) := by decide +kernel
theorem omega_spec_28 : coefficientsPoly omega28=omegaNumerator 31 28 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_28
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums29 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens29 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349]
def omega29 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums29 omegaDens29
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_29 : padCoefficients 32 omega29=padCoefficients 32 (omegaCoefficients 31 29) := by decide +kernel
theorem omega_spec_29 : coefficientsPoly omega29=omegaNumerator 31 29 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_29
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums30 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens30 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384]
def omega30 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums30 omegaDens30
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_30 : padCoefficients 32 omega30=padCoefficients 32 (omegaCoefficients 31 30) := by decide +kernel
theorem omega_spec_30 : coefficientsPoly omega30=omegaNumerator 31 30 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_30
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums31 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens31 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384,0x3c1]
def omega31 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums31 omegaDens31
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_31 : padCoefficients 32 omega31=padCoefficients 32 (omegaCoefficients 31 31) := by decide +kernel
theorem omega_spec_31 : coefficientsPoly omega31=omegaNumerator 31 31 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_31
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x16,0xe7,-0x604,0x1c93,-0x66de,0x12375,-0x29a30,0x4e11a,-0x7970c,0x9ddf6,-0xac398,0x9ddf6,-0x7970c,0x4e11a,-0x29a30,0x12375,-0x66de,0x1c93,-0x604,0xe7,-0x16,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 24 li0=padCoefficients 24 (liCoefficients 23 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 23 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x15,0xd2,-0x532,0x1761,-0x4f7d,0xd3f8,-0x1c638,0x31ae2,-0x47c2a,0x561cc,-0x561cc,0x47c2a,-0x31ae2,0x1c638,-0xd3f8,0x4f7d,-0x1761,0x532,-0xd2,0x15,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 24 li1=padCoefficients 24 (liCoefficients 23 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 23 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x13,0xaa,-0x3b6,0xe79,-0x29a3,0x5ad8,-0x9768,0xbd42,-0xa406,0x419c,0x419c,-0xa406,0xbd42,-0x9768,0x5ad8,-0x29a3,0xe79,-0x3b6,0xaa,-0x13,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 24 li2=padCoefficients 24 (liCoefficients 23 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 23 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0xf,0x60,-0x130,0xab,0xb5b,-0x3c90,0xb5b0,-0x18216,0x26f4a,-0x31350,0x31350,-0x26f4a,0x18216,-0xb5b0,0x3c90,-0xb5b,-0xab,0x130,-0x60,0xf,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 24 li3=padCoefficients 24 (liCoefficients 23 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 23 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x7,-0x22,0x29e,-0x109b,0x3f8d,-0xa758,0x13d28,-0x1b04e,0x18b62,-0xa24c,-0xa24c,0x18b62,-0x1b04e,0x13d28,-0xa758,0x3f8d,-0x109b,0x29e,-0x22,-0x7,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 24 li4=padCoefficients 24 (liCoefficients 23 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 23 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x9,-0xf0,0x6e0,-0x1a6d,0x37fb,-0x2310,-0xaf50,0x2b34a,-0x57f26,0x79b90,-0x79b90,0x57f26,-0x2b34a,0xaf50,0x2310,-0x37fb,0x1a6d,-0x6e0,0xf0,-0x9,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 24 li5=padCoefficients 24 (liCoefficients 23 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 23 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x29,-0x1ea,0x6d6,0x555,-0x8673,0x23bc8,-0x56fb8,0x89832,-0x8913e,0x3a904,0x3a904,-0x8913e,0x89832,-0x56fb8,0x23bc8,-0x8673,0x555,0x6d6,-0x1ea,0x29,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 24 li6=padCoefficients 24 (liCoefficients 23 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 23 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x69,-0x1f8,-0xce8,0x8fa3,-0x23715,0x47dc0,-0x34380,-0x77586,0x1b30ca,-0x2bec30,0x2bec30,-0x1b30ca,0x77586,0x34380,-0x47dc0,0x23715,-0x8fa3,0xce8,0x1f8,-0x69,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 24 li7=padCoefficients 24 (liCoefficients 23 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 23 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xe9,0x39e,-0x5762,0x18195,-0x1af73,-0x7e798,0x25d868,-0x4e3dce,0x593cc2,-0x286f0c,-0x286f0c,0x593cc2,-0x4e3dce,0x25d868,-0x7e798,-0x1af73,0x18195,-0x5762,0x39e,0xe9,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 24 li8=padCoefficients 24 (liCoefficients 23 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 23 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1e9,0x1fe0,-0xf550,0x1653,0x11161b,-0x42e5b0,0x6d6410,-0x1b1a16,-0xe61bc6,0x1e53490,-0x1e53490,0xe61bc6,0x1b1a16,-0x6d6410,0x42e5b0,-0x11161b,-0x1653,0xf550,-0x1fe0,-0x1e9,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 24 li9=padCoefficients 24 (liCoefficients 23 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 23 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3e9,0x8ba6,-0xcc1a,-0x12916b,0x55850d,-0x5c4af8,-0x11f8578,0x4556cb2,-0x623163e,0x306c2e4,0x306c2e4,-0x623163e,0x4556cb2,-0x11f8578,-0x5c4af8,0x55850d,-0x12916b,-0xcc1a,0x8ba6,0x3e9,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 24 li10=padCoefficients 24 (liCoefficients 23 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 23 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7e9,0x1fcf8,0x9b588,-0x62477d,0x509d4b,0x3786660,-0xb4874e0,0xadf8b5a,0xa2c9eaa,-0x245122b0,0x245122b0,-0xa2c9eaa,-0xadf8b5a,0xb4874e0,-0x3786660,-0x509d4b,0x62477d,-0x9b588,-0x1fcf8,-0x7e9,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 24 li11=padCoefficients 24 (liCoefficients 23 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 23 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfe9,0x6acee,0x55466e,-0xdda5eb,-0x5e2fcf3,0x17c241a8,-0xafaff58,-0x525df24e,0xab99df42,-0x5f9e8fac,-0x5f9e8fac,0xab99df42,-0x525df24e,-0xafaff58,0x17c241a8,-0x5e2fcf3,-0xdda5eb,0x55466e,0x6acee,0xfe9,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 24 li12=padCoefficients 24 (liCoefficients 23 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 23 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fe9,0x1574d0,0x1f01120,0x3f00db3,-0x2ef78a85,0x134574f0,0x1379194b0,-0x25270e636,-0x1f916de6,0x47b6ebc10,-0x47b6ebc10,0x1f916de6,0x25270e636,-0x1379194b0,-0x134574f0,0x2ef78a85,-0x3f00db3,-0x1f01120,-0x1574d0,-0x1fe9,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 24 li13=padCoefficients 24 (liCoefficients 23 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 23 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fe9,0x433c76,0x9b0a136,0x42322b15,-0x90ba1d73,-0x328441db8,0x7c89fd6c8,0x5242f7532,-0x1c99ab6cbe,0x1319b41344,0x1319b41344,-0x1c99ab6cbe,0x5242f7532,0x7c89fd6c8,-0x328441db8,-0x90ba1d73,0x42322b15,0x9b0a136,0x433c76,0x3fe9,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 24 li14=padCoefficients 24 (liCoefficients 23 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 23 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fe9,0xcf7368,0x2cd2b178,0x22fe97fe3,0x37313d6ab,-0x1c4324ee00,-0x1082681340,0x9284a0a13a,-0x4381793576,-0xe53470e730,0xe53470e730,0x4381793576,-0x9284a0a13a,0x1082681340,0x1c4324ee00,-0x37313d6ab,-0x22fe97fe3,-0x2cd2b178,-0xcf7368,-0x7fe9,-0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 24 li15=padCoefficients 24 (liCoefficients 23 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 23 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffe9,0x279d83e,0xc5f9a23e,0xf092c4d95,0x4b1a0e538d,-0x4017a2ed18,-0x2885d326718,0x1a6a85a2332,0x706da66ddc2,-0x63ff99ac84c,-0x63ff99ac84c,0x706da66ddc2,0x1a6a85a2332,-0x2885d326718,-0x4017a2ed18,0x4b1a0e538d,0xf092c4d95,0xc5f9a23e,0x279d83e,0xffe9,0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 24 li16=padCoefficients 24 (liCoefficients 23 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 23 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffe9,0x78486c0,0x350eff490,0x5d30548313,0x32e71c7ecdb,0x66a8746fd90,-0x11d9dc7b0cb0,-0x28fb6743da56,0x346655aebbfa,0x4affb3416390,-0x4affb3416390,-0x346655aebbfa,0x28fb6743da56,0x11d9dc7b0cb0,-0x66a8746fd90,-0x32e71c7ecdb,-0x5d30548313,-0x350eff490,-0x78486c0,-0x1ffe9,-0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 24 li17=padCoefficients 24 (liCoefficients 23 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 23 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffe9,0x16bb9246,0xdf0d5eb86,0x21ee44ba195,0x1bc2f4ec660d,0x7ec236240f88,0x569bc6bb8308,-0x225fec5dce84e,-0x257bf12bf813e,0x38a6ffaef51a4,0x38a6ffaef51a4,-0x257bf12bf813e,-0x225fec5dce84e,0x569bc6bb8308,0x7ec236240f88,0x1bc2f4ec660d,0x21ee44ba195,0xdf0d5eb86,0x16bb9246,0x3ffe9,0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 24 li18=padCoefficients 24 (liCoefficients 23 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 23 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw19 : List ℤ := raw_ints% [0x0,0x1,0x7ffe9,0x448eb4d8,0x39ce8dd068,0xbdd23e87343,0xd89aeec4340b,0x627dcad7367a0,0x10c8de45907860,0x28609f5c8fb1a,-0x32fb5b97c6c596,-0x2a7d3fc337d3b0,0x2a7d3fc337d3b0,0x32fb5b97c6c596,-0x28609f5c8fb1a,-0x10c8de45907860,-0x627dcad7367a0,-0xd89aeec4340b,-0xbdd23e87343,-0x39ce8dd068,-0x448eb4d8,-0x7ffe9,-0x1]
def li19 : List ℚ := liRaw19.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_19 : padCoefficients 24 li19=padCoefficients 24 (liCoefficients 23 19) := by decide +kernel
theorem li_spec_19 : coefficientsPoly li19=liNumerator 23 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_19
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw20 : List ℤ := raw_ints% [0x0,0x1,0xfffe9,0xce641c8e,0xed63c17f0e,0x40896bd23715,0x629b78ac38a0d,0x3fa30a23f2d428,0x12867c727ad1128,0x23ae326df34f2b2,0x60661e626ef642,-0x409bf45b60f2aec,-0x409bf45b60f2aec,0x60661e626ef642,0x23ae326df34f2b2,0x12867c727ad1128,0x3fa30a23f2d428,0x629b78ac38a0d,0x40896bd23715,0xed63c17f0e,0xce641c8e,0xfffe9,0x1]
def li20 : List ℚ := liRaw20.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_20 : padCoefficients 24 li20=padCoefficients 24 (liCoefficients 23 20) := by decide +kernel
theorem li_spec_20 : coefficientsPoly li20=liNumerator 23 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_20
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw21 : List ℤ := raw_ints% [0x0,0x1,0x1fffe9,0x26c9c53b0,0x3c81b748b00,0x158159dec0c73,0x2adc0c7349283b,0x2511683a5e92030,0xf8e855f227eebf0,0x34fe96684e7f758a,0x57faffb85bba59da,0x3074f74488b60310,-0x3074f74488b60310,-0x57faffb85bba59da,-0x34fe96684e7f758a,-0xf8e855f227eebf0,-0x2511683a5e92030,-0x2adc0c7349283b,-0x158159dec0c73,-0x3c81b748b00,-0x26c9c53b0,-0x1fffe9,-0x1]
def li21 : List ℚ := liRaw21.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_21 : padCoefficients 24 li21=padCoefficients 24 (liCoefficients 23 21) := by decide +kernel
theorem li_spec_21 : coefficientsPoly li21=liNumerator 23 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_21
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw22 : List ℤ := raw_ints% [0x0,0x1,0x3fffe9,0x748b4f916,0xf5832bdaed6,0x70f9e52003e15,0x120696e20500f8d,0x1430a3db518b9cc8,0xb5b6370ec414ff48,0x37c03514c8bfff432,0x9d1bd88346c3fe442,0x105e832482f4889604,0x105e832482f4889604,0x9d1bd88346c3fe442,0x37c03514c8bfff432,0xb5b6370ec414ff48,0x1430a3db518b9cc8,0x120696e20500f8d,0x70f9e52003e15,0xf5832bdaed6,0x748b4f916,0x3fffe9,0x1]
def li22 : List ℚ := liRaw22.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_22 : padCoefficients 24 li22=padCoefficients 24 (liCoefficients 23 22) := by decide +kernel
theorem li_spec_22 : coefficientsPoly li22=liNumerator 23 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_22
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x17,0xfd,-0x6eb,0x2297,-0x8371,0x18a53,-0x3bda5,0x77b4a,-0xc7826,0x117502,-0x14a18e,0x14a18e,-0x117502,0xc7826,-0x77b4a,0x3bda5,-0x18a53,0x8371,-0x2297,0x6eb,-0xfd,0x17,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 23 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^23 := by
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 31 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 8 32 at hb
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
theorem cache_li (j : ℕ) (hj : j<23) : coefficientsPoly (cache.li j)=liNumerator 23 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x7b04940ab1dc6a835bf347bf63ae40bc000,-0x1138131fb3864a054a77bfa60816ef1da7000,0x12c5cfe5dd34eca42272febffa382af7dd4800,-0xd467311eeba0ee0a534360b346eec7ec7ddc00,0x6d8617c7c925f733b910a50b1e365adf2ff9e00,-0x2be463e533a6ae39d6ea500b3430ce698deeae00,0xe3aa1201b0f17fbc1d458087dc772e9d82fc7500,-0x3d5b300d270cd14192477347679560b9c3165e000,0xe053c65c67129bc6fe506d44f3d4bcdc4d40e2f80,-0x2c1c8e4630c6928d39cb7382d8ab85ab01d518ab80,0x78ccc54140f2a1afcf52f26a7698f93f0dfbd5c7c0,-0x1228a09296d83166e8b0a393b6301eb27ca0b1ff340,0x26a20170e9eda175684f238d554c0333deae7d07840,-0x491fce7c895174d2b2de35ffa2640e2e3657f1d3cc0,0x7bb66a488ebce11bc72095aab10ab23f26ea48059e0,-0xbbc5dc67fbea7547fb2acb044ec56b711fddd497460,0x10073e0f91eb84faa861a0cdf1eee00afe0780bbf180,-0x13be4f6cbdb5d001374e115504d29b4ba65af108c040,0x15f8e310e7b0be287bdb684c07fb430e7cd087cfcc70,-0x161e9b03aac84f0c26eda26078b7dbaa940fa2ccc350,0x14289050bc492a5280cae6175b519d9330d2c004a490,-0x10a2d347582aed915876b3bfc3a771b0fafffe28abb0,0xc6e4a6d138d64d894e7bdc33fd1acbfe8f041d24118,-0x867d22b0fa2186d5985de593e41e9b44db7bc54a768,0x523665cabc41f72e72063b61c15f7264aae02c0e758,-0x2d5e1e10ec871b18584b9c133be5126f6ae3afb6828,0x168e786e820d3282333dea5ecef9fe057fff3ba3078,-0xa146614274b749c255f92909327d3b6be9a9028a08,0x409344507b9f0f924900f0cc7ae36c68ca98ff1438,-0x171508fea233c711620ee7104ffa865efea74e4948,0x7551c42022ce33c15272ec98ca4e567421b91a4b0,-0x20f1693f2fd527000273832f45dcd24458075ef90,0x81fb3fbc7d702033f42ae68c4d12bffb16ce6250,-0x1bee63d68630776cb9513f60f1f18be4ffd23970,0x52e458900ce74d350c45d889b2b70f65715c900,-0xd1e40d9b706b5f289e711d4a2ebe9dc08cf0c0,0x1befcdb5e909bb96441a0a3b413b741b25cd20,-0x31244d370d6c5dda5693dc2177e0abd35e920,0x45c33c21ceaa0e18f9712ebfb373254f2af8,-0x4d84f546c2899c156bfc177d1939e030408,0x40abc79b556a5eb409258e9075dcad1878,-0x262b6b5f05d02c32136d88cdcb3eeb088,0xe90e2bcdc898c838c6895577e7ea4b8,-0x318bd18d8448cce18dd08e79285548,0x46c06713df904107a33955d8c5b8,-0x15275f0ea2a3f4b70d455f7848,-0x10c048c9967cb590a9f920,0x6e5c39e4d062ca4fab1e0,-0x24c968a19acb98c5390a0,0x9ae43f4a1ffaef088460,-0x1efa730ed3322fce80e0,0x46cebdd8be2991d8020,-0x66fe2b69cec819f460,0x47a5aee56e74f0aa0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 24 42 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 42 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 55 indices rho q0 m0 0 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 55 indices rho q0 m0 0 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0xee58ded4b89b0e5e82275b02d1219d6c4000,0x20f80e5defd0b0315e674541534cbc1ba47000,-0x23834ac075b6f2edc43d66bbd1c8ad8fd272000,0x18ce78e972126851e2ee3dbc1086aa84d1888c00,-0xca1d9d2bb1ed563bd5b26546efc03c65b15d8800,0x4ff8f06d3ba14ef060f4c47a2fce16f5b38129400,-0x1997349e0c5f28c9374de00039a2fe3b44f45a1000,0x6ce4d742efd4781b17318ded399e42b68f6507ab00,-0x188c713ed0dd8a50a02ccc3f053083a35cabb48fa00,0x4c2cc3d3e777c468b62f355328b9b88003f8ca03100,-0xcdadc52bedcee8173c7b8bd18e9b239d3a3b051c400,0x1e796b504e0ccef18ce0c77dbc5c0404f767c4d1c700,-0x3fe218635335735ea734adaeb2f625a65b274b7e0e00,0x771a2c8396680e78f348daeab20700f9587c55eb6d00,-0xc66633ed759915ca442678779d75fe36c6768f1b3800,0x12862a5490759657ad39477e2eeaa1cb3c24331c25ec0,-0x18e3e537860303879b9a1465f0534f2c4f1030cced280,0x1e267385fa1739ed8939d365e9f880c8e80cc98998440,-0x20fb2e67d422a83a518a4b4fa66e8ad7f0654cdf51d00,0x209e952b7c496f28027e8e878cfa41f5d6bac7238a6c0,-0x1d30a9cc2116ad064502b29a6cb6f72eee84465243d80,0x17a401ff734e72df93dc0cb5132be768321e61d285640,-0x11533c30150d7636d9db72056c07981b7e47c40442e00,0xb7b72e64711ee6cd402b84b6650b25c936ee34af17c0,-0x6dfeca9e3ad13ebc9b3bfcc8db9764b6c46c5438aa80,0x3b67d47ca41df2e295ef0634865a84667338a1184340,-0x1ce1f8d655efaefd31cbc63f0b7ef2fa892371c94700,0xc9c14ac26d9b8430ef8e25312486d51f77b230173c0,-0x4ed8dbe579cdd8a0fccffb2c75a75d5cb609f1c7980,0x1b7a5f07da4638e48dbd2a12552c7ba9393bd9b4940,-0x88007928c3ddc65d639bce074eb587c67dd34b4c00,0x25236dce1e6197e8d38a5dc12241e7d562377e8440,-0x8e4a4fc52ebc1fe248e446fe699e52a4ee2468380,0x1da3f153308c5f7a7e7c214d6bfeb03732a90ecc0,-0x551bcbed8010fd3cc93010e8b49c1c0333a50b00,0xd00c5c04db8cd109051ac8e1d1720ae52ded840,-0x1aaa514846c1458183cb4e383deece9d45fbc80,0x2d0824052afd694b3008c8bf601dfd47b516c0,-0x3d27d1e8fa6b801a1a7c7c027eb99a0a0de00,0x40ba1f77df277e5bbf877cb6778f8f4c4a40,-0x33289a19cb08eec344c8c4deb1400e34580,0x1c698cc1a4a2ebd7333d033877876c3ac0,-0xa1cc3937bedf7d398dd1b518c2ce0d00,0x1fb31bf97babb21462a244b5908ca40,-0x29088757a2ee0eb25386d724d7680,0xadfee177d62ee43aad51d5b8c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 24 43 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 43 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 55 indices rho q1 m1 1 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 55 indices rho q1 m1 1 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x1cdcc2fbc25ac6bd71c2c405575312101bc000,-0x3f24014cf81dc6d4ff62b1cfe4313c7faa3d000,0x4336bed96957e468ecd9b3c032c7caca94ef9000,-0x2e6383006ea43dd77a6b43abff66d684cfb566400,0x1755a3db806662a38a5713a66eae69bebbe86d3400,-0x91e3fcc3abd03862e6bb130ef1a653ecd72124f800,0x2e179550a70f39a774d57cec318ba01e5d0e7ca5800,-0xc1982ed4f3436bdc4762beff41607a91e79d3d79d00,0x2b110985dff454587bf80a3029ce335d5157e9b83100,-0x83d52dbe30ded4bb0b3e14a665168b63217eea140e00,0x15f0c76756341ff4cf5aa656fb43ea8bf42c89c182600,-0x334768d789301067a19a9bc4e339e823af2d2ff120300,0x69f17d83abb304887e40da1437e19e2b28d9e6d6f6700,-0xc298ab12a2f91989908e0ca25caa82cabff61502f6c00,0x13f3df73fcdb9555eb252e11baa927f0e68ba889eb8400,-0x1d57e92346ebcdf2fdd695dcea632ed199c0be9d59a540,0x26cc65aa00b530dd0eda8a62364d686874be40fa335a40,-0x2e3a13217be9c99a7361de7b6e4af5d382d268d7a8dd80,0x31b6eeb3292bb143d0cb8b372e51f076335b0e148b8380,-0x3050d8f69b349838f0f065815ff9b95465bcbce0a621c0,0x2a767dfaa663763a7f602bf9ce576dd30f03add98666c0,-0x21c1694467f2edb6e13f55566931709992a3a568d41300,0x184431a2af2f872a77d52dd143f452ca99429ed9cd2100,-0xfc3fa424ce67fb6102d8849abbfe36ce1a38fd0b16b40,0x93f1df874d36728345d5d348d5c0be9335a31a2078840,-0x4e35947b10a1c62f3495b86a477a963d850a7197fec80,0x25303b327a902a92fde5e087d04ebedf1c4d581a63680,-0xfdd2eaab131fba4ffe744b98d43aa6441584370565c0,0x60d38e42c0e3dc96525fddd8d6ced9befd6254800ac0,-0x20e6aea70893bec759ee293728a29a036460cb7e6000,0x9e94e6645d2896e17a331c87947afdfa057eea1ba00,-0x2a1d03a4090196dc80d3958e774336ada11fe9b51c0,0x9cac4c6ba84057cc7cce40630896f7c47230bb88c0,-0x1fa2ae5600fd7ece0b739315b6070af233846a9680,0x57e0c618375c23b47dc0743421be99784c5546080,-0xcf59ee3e4e86ae0a7d49e691f20d41a06c357340,0x1995c7519014291fbcfe63045c877e41c78b5a40,-0x2977fb013860475a4e69300d129c452523fe700,0x35da34431d591f97b07b5c08077dfe98d1f900,-0x3642fd5cb982995a475c561d519cae9cfa0c0,0x289ae8b9b17709a10c5607d43473d90ac3c0,-0x15341c7792988f9f2f9911f720f2acb5180,0x70833c3c1411700e324287893c1c37f80,-0x144b7a836a272f8da2208afc9df0fe40,0x17cb366403e6f8a0d9d0a373747940,-0x59694b5115afdcb7c42bc7ab200]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 24 44 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 44 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 55 indices rho q2 m2 2 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 55 indices rho q2 m2 2 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x37ebb9c7c88fe10f0c695bca5930f2ff35c4000,0x78f420c430bd65f8b4b51c51455ef34a4da9b000,-0x7f467971c0262c45ada9a79fc2d52cc48470d9000,0x56cfb4b12057dfb18e6fcbe8ff9591490260489c00,-0x2b2564d4404733d4bc8b9d9d1e92639d4c6bc3f5400,0x10a7758d29fec7e4cb8c12bee1b5477059b9b3a88800,-0x53238efe36748d1801fa8acfc4fd91f944f7f7d9f800,0x158c2cb88a165f29409adf9e1be619dcabb9087ae6300,-0x4bb3078602fd08da4ffb1e5f325a3181a788c6bf41900,0xe4a6fadbadc2c2cce2f816c161d724fae4dde98b39200,-0x2589a31a7dff24819e96d82ca048f1825d1e5cb71b2e00,0x568394dfd158e9a1704b18e63eb6925632eff012e85500,-0xb032b8447dc3bb6a18834983501421d1fb7c6d70aaf700,0x13eec9e0b836812ace90089fc817dbdf2d2e739a13d8c00,-0x203634adeb462c1161c55ba31542d3f4bb7ddbf2b019400,0x2ea55127e215e008753b25a3bbe3d6cf27e5ae4e66762c0,-0x3cb44fe6e6799218bd43870f8709bb43ec57b4afa31dc40,0x4727d04c69f08f31d5526f11da8b667dd09e89417c4b280,-0x4b3fa9dd6bf58c820f1c266b980602c000c5d9b17754d80,0x47e040a236b798dd9878f089efa7efac2b5353025b64c40,-0x3e0cf9153a357e9cc51e17339bb80629c9c691c9609eac0,0x306cd831eff5d3e08f87e71e263b1d0790fa9a3cd676300,-0x22278ff8db86d6fc83922e8aa922132df86baedc7dc8500,0x15c17ecaf0b36309ab67ac3ed72c7c8aa8cd8fceabcb4c0,-0xc80528b9ceb839868a724be93b51bb2273143efba0f640,0x67836475a793b618aae2e6613b149539a0d29f0b507b80,-0x3024aac82e0fb66b83aa8f197bd41072695b5876258c80,0x1411a0717e8881a8d8deee92c5f7bc19f1bb657eaa3040,-0x77931a5d23f4edd35fe500d61ec9dbf13d230994892c0,0x279e57a014fde3211cf76306ff0c95f4a9dfdca22de00,-0xb9f7c1eea57c89f6d24d35719942e97bed203ee3c200,0x3007266cde44965027c3722cef6fefe9d3c5f7b0e640,-0xad7dac5aa3155b3b82dfe13c869b91fe1c0844766c0,0x21f45384daa861e62af96349738f3905625dc39f980,-0x5b3c68a85d590ba6b0366e757eea391ca04366d680,0xcfc14796dde7edb5338b0ee310d149de0749466c0,-0x18ac50070ffd1aff09fa02ea03387310b643b5e40,0x265e6e3becff95acee8755405e06da919c708b00,-0x2fa082f79d5f41988a4af544778db3c6d969d00,0x2da97d062a8b9fc1ff0f89c5b57e20743e7f40,-0x2054c0431712fe2702c214b461539fbf8cdc0,0xfdca0a3fe30f51b59f38a43efe1a91f8680,-0x4e5bb5e15a2d7fa162a65ce44cff0b2180,0xd0026a48611cded1ee17a86265604bc0,-0xdcb6595dad9251e5e4d56a84bc7940,0x2dedc8fe2852e3489511b20b3000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 24 45 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 45 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 55 indices rho q3 m3 3 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 55 indices rho q3 m3 3 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x6c58b7f31496c40d280c21d80cced6ce782bc000,-0xe7c1f0325c75e872692df2009d7f21c37fa555000,0xf11f9a152e4bd3388901e059c1bfb09bb6ccf2b000,-0xa2935527106391fc3923ee5fbae4d25eacca23f4400,0x4fdadece021a74f36ac3bf7cf7cfdfc69aed2461bc00,-0x1e747cf504ad83461118c50633ec2bfd52b80f4dd9000,0x962d9c1d55740161ce729cfb3cf918f1a1337122d3000,-0x266fe4068b4abd02646d99dfa43d3778a62f071baf6500,0x8550238e03cbd6fe22080ffb285250103a375863aaeb00,-0x18d6d380e59faba2184ec9f18dd0b9e33857e801d8b7c00,0x405fee94f469be078988420cf7b37fe599929682e5db400,-0x9256d920928252c1b859e44e1ed0d890bc1e03e4e9d8d00,0x125de63eb4eae3c954266446ca151123c3eb3075c8636300,-0x20c46d753a58d2e1a90aecc4384c42597786545776fa5000,0x342c2fca28f2d1c7a9a8dc041363174f815636eb6aabd000,-0x4a687da34ac2ac7312028cbd1c9eb2c03c42813401e31940,0x5f541120c4b72736af6e568fa47db74819d378079c3daac0,-0x6df401ba5356f54df123ea28163b1505f09080e65eac4f00,0x725cd83bdb8cec957e9711c3f003bde6714628bcce5d6d00,-0x6b61c570ac7011e098f51a3c02f5abacde80063188521640,0x5b1419334f6bd3bd6921fe04e9c53beac440aa800902c5c0,-0x45cabeddbdde81ccd0a43eb54dd52b5e258f476af2ba5c00,0x304d7cc539515b0aa7807700d94431db5a3e67f152b2ac00,-0x1e2bc51c4df8b384fa97e1a364fc371aee50547a4b57f440,0x10fcdd5af3b41c7dffe1cf9f977a77cda27ec5dcdf5c0fc0,-0x89b85cb80c7420ab7cdb06a470574d2797b5b2a80f35300,0x3ea86ea3b0eb2f5d5e7c4e12eab059ced2432ddad68e100,-0x1986b991f219d202aacbc6f612b01ef180357196ebf2540,0x947b37b58048e5e66e9e36ac52bdae1429de29f43e76c0,-0x2ff91428e6839ca9c2cc25681f8578dfe53d979c582000,0xdb4d8e001252e4a2dafa743e15e3558798bed812bb000,-0x37144b67e0e1c06c172505f19513c1bff336773d993c0,0xc12e1a3715bac503428c35d0a89235da5fa9cc975840,-0x24a48187a2482e9a313913217bee380ef60541fe8500,0x5f3a6558bb078bc82e7ccb678b239531a671e171f00,-0xd13ba06e0c0480473968debc92b359723584e2e6c0,0x17e90f4ed9bca11353a0c08e88057dd3719d26cd40,-0x23a9d4db62828f7fd7bfa140ad1c813bae046e400,0x2a4bf4df3fe49e476621cd8a271489dacc196400,-0x2690bb8694df538d772b0e2a5e7a1875a1149c0,0x19d2035a2666b9154cc4825228570b26ebf240,-0xbe4769979afbe70ddc721aaca82a37ff4d00,0x36a595bbdbdf6bb65f4ad1cbe9a09b96f00,-0x854fe42f9e62dbf9a8a3201c90f31bcc0,0x7fee50ab7fd06285c3ad9f072272740,-0x1795912f66fe4bea6223f00788000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 24 46 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 46 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 55 indices rho q4 m4 4 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 55 indices rho q4 m4 4 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0xd1ebe466f7e41bd97d97819298d0c03008d4c4000,0x1bc2c84b7477179c2b08539c31a71c0e56883e2b000,-0x1c90718b929d968b0c547d7e7ed15891628d8f9d5000,0x130ae3c6f50588fb3d736018bf649c6531081871e5c00,-0x93efd62518cb41098cbe9e7735c5bc36a66824fa94400,0x37c234f053bbd79b616bd1473f903ddd97e93c696df800,-0x10fa928b17eb50ae9f295e3da270649bfeeab761a138800,0x44adb4fee8bffc67d757b143a25f4e9c9a92e456346f300,-0xeb37f9b4469a93a6bf9fef9f8c68763345dafd4a824a500,0x2b43d30aa0da739bc7386d5f1809a4b28ad90e8a3a2e7e00,-0x6ea83ca7240b323a9c7566a5adc21908286d394210b5e200,0xf82b516fdce62e4f3c0a2d98a94af58ad7838ecce2c5f900,-0x1eb7d1e4a9a0ab362c294fd85b32a8f7b59ce2307710bdf00,0x360711f78f02031aa7d2ac9d15f9a0020899454a4a26b2400,-0x54c648f7af89e7999b79a93c93e028abd04631ad7a4035c00,0x7719c545106ecd5959a10f255146bb5e0c39aedbab9e17ac0,-0x963e94683786d53e133d4fb22c6e994420bba889cdcef5b40,0xaa8e4ce7ef9fe6d42ea9c3b8389e4531dc307d5893b6df980,-0xae81d2422a55b3c7a5533abe460354075ed967d2e47357e80,0xa11a44d9c26c223637dcda924388e9b9bf9027a774c3b2940,-0x8645bbd89d0117b0f2bcfa11b4165717ef0f2bca2a67bc4c0,0x650b85e2e52b70b70b42bfdc4c026e95253972338adf85900,-0x44a247952365f59c8e6d3b8056d34e8b183e950e50b270700,0x2a0b78232c03f61fabf7696319d3ef8df3a2b6dea8f6406c0,-0x173330259adfac7df2b4ccca82b2fa3e5d9e9d4bf2863b740,0xb82bd4ceaaf130211235413c4d5bac2b688ae075df673480,-0x51f9d7d6e624af13befc4366d6947e878b4207ce9aac2380,0x20a40b48f47f155857bc407033e79dd581660187ff473340,-0xb95f2e99de3aca2b89d5a10435c7d97b8db86dfaa9ac2c0,0x3a67d34c7c83abeef57e69b48c4d197e04ca6c08605ba00,-0x1040713c45ca302d89e73ba8d2107909eaeb6dc19ed4600,0x3f82ba2c9939a408eb224e339e0b762c9c875c12ee3a40,-0xd8449f507fa06123f27e05610efcb368826b2070547c0,0x27c1169a5425e37f509ce26f1ab4c75560c8fcac27280,-0x63e9367aeb9be3e48a3f1924ae6cb9b99a4b36c9b580,0xd3c67f7387681e98d5b3aa826438802fa3e283049c0,-0x1748000e93679ffec6737797ee8836701aa2378a040,0x214b89ea34dadc36fee7d2fcd4c1edbae3478f0100,-0x25b68a31ed97e0ac78adcba8b457bcc5723269f00,0x20af4c945256950ec62f16d3c29a71908aee9140,-0x14ade7e2722cadbea8128006df0fd4549bd00c0,0x8ef5d0cbc2f47e82cf44c8b25b5dbd37d0180,-0x26287bbd485e5d3491eb17b7a2341ed7a680,0x55792ebe85a97ec3f342d5e67ee127c4c0,-0x4a228a1c9d67fc2691dda187e10d7540,0xc1b2c729ef543001bee1b784c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 24 47 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 47 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 55 indices rho q5 m5 5 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 55 indices rho q5 m5 5 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x196b90a878049f5f563558b0c0814745d111c3bc000,-0x3537b2f63cc7c49c69ee3031198a9d6c268c03175000,0x362aa26f9d920da3f94d78c7d99280d086c0f457d3000,-0x23b66fd5ed71bc7e61ffce3a3d475858233b6935654400,0x11252514bdd3beb351139c2dae27a0849bfaef27ef05c00,-0x6634a6562c56bbd559704bb8f649af9c5b601209bd65000,0x1ec1ac0117d93a337a767a145f126a53187541133c56f000,-0x7aea0013a6a48c85e1443756e7f0e0bf6cceffdffd5e8500,0x19fcb84f5cf4947d23b5ba5d2c12e193e644c8d265007d300,-0x4b843283da54dabae27c5419b53607bf46634d8e56b4e4c00,0xbea778eafe722cebdc747912b3fc30ff53dd8ce47f0c80400,-0x1a5ec3c1d29c38973da4ee306dff25b8369122dd280c156500,0x3384356b7f0affc77ec6fcb1f0d53ae579c289ca3a2d602300,-0x5958998cf59c54296ca995f7fb3625e24480b39c79ffdad000,0x8a2f987daa9c02f37850fd84b93108bca3d693721e1cac9000,-0xbf47f41de738daa756abd3babf381814e7fe40c0fe2d81b940,0xeda4b1847545998790b5512212d9b264cd7d96674098ea1cc0,-0x1098f1a0284319405506d922a1912d6ec1b86d9f1cb3994f300,0x10b56478a0148b0b223a8b6fcaa95dd729a846199aeffb49100,-0xf2b33904234e3a90bf6bab8fd3172e75f27e2219824634c440,0xc6ce45eb9743fc6db16506f637b62dd583ee3f382032b785c0,-0x92f301d527f7c394df7d1effbcc9058cfd0648c855e303dc00,0x61f9af8880113f7cbf34d2411006323f8e3cd0402dff557c00,-0x3adf3a437c9dee930f5ed355bbd0fbaf8e9f3c44b9220e6040,0x1fd6f78cffb4a23b5622f33f8a223550a0cfffcf176ea255c0,-0xf787bed22a6ced94a3a07b9683b9d0ffea42e5e60e540e700,0x6bcd1ddb81eea4a5a9e2bdd878f4714b86304ee9e4651e500,-0x29f4d50e59984f1e4ae322038dc848b96eb872f1328a27740,0xe8a6fe03adfd5441ff8e2b9f473884099d30dc0375bc62c0,-0x477c727a4f50c682b6f42eb1f921162a89a6f0b38e9b8000,0x135f6b0f50f739558cf8995295f55e8c2547ec513f79f000,-0x499f8496e19ba30015b015961a9ad8e3394ab5b9fa4dbc0,0xf364cba9ea4b078485d8f95349f35b2ad331f28c073640,-0x2b5a96d73a243a6dcf3599d7da954dcd39f2a15f909100,0x695a696432e962ef2bcc1a8afe5e417e9ff35394b0b00,-0xd763734c4abdd16e8a078766e568e7c0af048bcd78c0,0x16c5d0575635ec0e1753df325ac1f1bebae9beb69540,-0x1f375b27fb1c5eacdd1867a1a50facd157686a1c400,0x21c141ddaa93725a663ab8b8f13303ccd76ce95400,-0x1bcae17cab4764becce48090d9c7868ab797395c0,0x109b344b83967677a5f8f2bf5a7ff007bb35b440,-0x6b9e1388f5b0800621cf10445cd9e83f39b900,0x1aacbb81f2c74f52a5f6d6b0cf89692150b00,-0x36d1d1b6c5b1ee5839f1b8ee7459ac192c0,0x2af32b0a8a614e6bacaa76e4be5101340,-0x6364ee8263b87f972ec6b703200000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 24 48 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 48 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 55 indices rho q6 m6 6 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 55 indices rho q6 m6 6 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m7 : List ℤ := raw_ints% [0x0,-0x314068466888f4c8b7075bd674fa7a1745126b3c4000,0x660abea8aaa0f9ceff87d7fdc4ff64403c9ad9f0ab000,-0x66c3afe82f017ad8d166effd34d4b0a420ab38e5fa5000,0x4305db33194d28ff5e6d66d459e0653aa1de3b82bc7dc00,-0x1fd26f647c5cfcd9a296782c3bd8e4980efcd6bb36c28400,0xbb8f863ebe5bec52d2939998857176d2085e97e8f9449800,-0x37cab469eaa2bfbf2736bc280838a187169a86e95cfa2e800,0xdc55b1c93c9b0f64c34c95ceae774f58c8f6db7025ef73300,-0x2e059dff807d9a45eb54efda0640e7a8c22b3e7ad259c6d500,0x8414c6380e9c223c2613b2bad179394bd06e9e0807a074e600,-0x1493b84ff213ea3861458bbe08aa2e2cdeaa4e747d08bef7a00,0x2cf1ecbf1e66a49e80a7cfc303a4b55ee4824d4f464d3c91900,-0x56a19310cebe12a91140767b9a8f3066d9caa0fcee921c46f00,0x942f2f9882b664f74e0c2e6c4b76794d65f6a3d4bec43b8d400,-0xe1f3fcb0e7de6795e720dce6c04697fc52d4587f68c36afac00,0x1343a938d98df9549c9aab20906cd827d823ee74de6b1c414ac0,-0x179355c6d68c66781affadce013a78cae83e6787627e6df36740,0x19f048aa7dc623e0dd5f00407de8f96156666747b8c0abacdb80,-0x19b25756be3e8ec4f62f529f0354eedc878706a8e8dfe2e8dc80,0x16f1e313f686e11f823dff064c123ba39f11e13e3f265ecd9140,-0x1279b1ce0bc78000ee75ca7ce664091073e350249a038bfe18c0,0xd6a67eff41f2234e1119db4cfa952eb4ea3c8b7d4c4b803c500,-0x8c7fa8aaba7d6ed1340ccf27ab7303a2bcdc5b9f7c59f5b1b00,0x52d24f9e86cfc95173392843bc0f0240ad12563100fe7acd6c0,-0x2be87ac7a8e6cf6a7dfeb3b40823c9ab9f248777776c1939340,0x14e54f7991623c0a64e92f89743398e55c1c6c113634df38a80,-0x8e7a419d22f3c0f0b8c9751778a47109cce0c4de4c08328d80,0x3634fd0a6ce67b468590c2f6a89acd1c48c3df46171f25cb40,-0x1258184ac97b9c7b4df2e3e79b2ac690297fbdc08741e6f6c0,0x57f3f6f1d12ddef29f8e5c00a2e7a32dab0799b64204ab200,-0x1736bf3fc8c00aa82088303480bac5b03157ba310fbf94e00,0x55ca4a296a2783aa6161500fcf1574956912dec08b0aaa40,-0x1135519d30c3b6f7994e8a681d23ab16511fd6c03165ebc0,0x2f84ab0a56f8a8cf8612ed3b85e9d332978f71aedd4c080,-0x6fa2fc808978095571bbb56a1ad8f2b6174cbd53282780,0xdc17e81070a387b4d78e739ab9d9a5a43987dd8e721c0,-0x165fc495e626656a3a29f7e247cd18032550faf703c40,0x1d63156e506868cf4359114b54ebc4f51eea77c50d00,-0x1e52b30cb8096da28de2c6951fb7207cce1227c1300,0x17b4f6f3d309aa34059447e0b26d395d92fbedc140,-0xd5e7d9af9293756d8a108c2438d87a1799fcc4c0,0x512883d50dd7532c9965b548e749cfef5025380,-0x12aa8a73b0a110123c842324b4b24a0fa79480,0x232b30ad805b4968878a9f68e9ae93aeccc0,-0x18e05b4b597b00787fa4402abb663f0140,0x32fc72c2f01233363b48a8f03000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 24 49 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 49 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 55 indices rho q7 m7 7 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 55 indices rho q7 m7 7 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% []
def r8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m8 : List ℤ := raw_ints% [0x0,0x5f6cca086a895a44e29e41ef82a54c8d15d3afc4bc000,-0xc3b49ec081b80024f5629c6520441e520305bbaadb5000,0xc30dd48de9685f93238f105d4e17fc51039a2ab3e453000,-0x7ddedfb258a03cf46bd9dd7bf5bc158a7d9aea555187c400,0x3b1e06c3b19dfc53ef7f666e3edb7825bdf54b0ba88845c00,-0x15897b81d907415fcab15bca1bb70d73bd63749758f8bdb000,0x65581c4d3fef385cc5285137ebefe4089ea916eab2ba8e9000,-0x18b99a0127783ab92534bfdd97d51140f2fbdb15aedbf19c500,0x51a682f13f597c7a79cff1519098c6f3bc85952979bddf4b300,-0xe77c353feb3038a2f09857e7ed2762e5906d4a5784018222400,0x239d134c454ca6a1197f777a26640229dae8480e355a69c5ec00,-0x4ccae4da0f3ad73601a74949ec60024a2142bff3bcdb57d02500,0x921208b19fe76f51cc112c52940578a3eefc6cca15b7eb284300,-0xf67a68881476481eeebce0c579a69092c21af783f08bc8097000,0x1729a9572e82562a74609777380403f2ed87ea9e0674a4f167000,-0x1f24eb822d14a2673e772ad62d1fde18a0328f911ce94e909b940,0x258d1a99ce6e1132941e1b408ec43cf4ff155c12a37307d41e4c0,-0x28af7e7c26dde777bb911a00e93a6325197fe9b0ed38c37bd0100,0x27abeda888253e9559ccf7ec631791e19645048a0e47bd6a8b300,-0x22d8c6008508e88b5becfa4e0ede2989b171c0d708eb6b1a91440,0x1b960b276ce24c82029fbd677618585476a1d5391c81cb2c08dc0,-0x13ae73af2bcf7955a3e500dc525e8ca7aeaf5a7bff5519389f400,0xca61e0b422e5fe02dec359fa5c5ba23ccb1b06147ab8d1958400,-0x750d81f2ea9af3fc715480619b63bd814e651c067d9aaddfb440,0x3cd6a29f32baab16659b3a0572431dd97ac3a018fc969b40c9c0,-0x1c5c41c0c6e7eb8db9d3817330026b2758da67bed2d36586ed00,0xbd3d9550c44cdcb4fe938dfa72fde8e37274822a3eb8892ef00,-0x4662f8896645b79d2168d7b8ec5b8fdeb5c158a27b499f34340,0x17428709413123a438a9d06e87394712f291c2d05726b45aec0,-0x6cc41fe49a9f6e18532b5742016380a1fb3b3dd385f8a40000,0x1bf577c6081fa837ca043d6a3d6007da0d4e911da84808b000,-0x647a0020c6125b0cbe021ec675952123dd565c6974fa263c0,0x13906dd54cafbbf7896bcfe8d263f8a01ccd1d6aab5e0c640,-0x3456bac62eb5c40b9de294fd3e0fa6a55caf955a1f32eb00,0x76dbd359fc2582dab39ae948a703579590183e376e10100,-0xe1ed1554e729da6628bc0bb736f184081a02b4aab3a0c0,0x1613a0586a6a67bbd98021e8d89dea40b72030667bb540,-0x1bc62837d670eccc70dfbe591b61ed0163b459ca92c00,0x1b55f3a4d1e03d455081a3868dd2fa83d5bdb2df0c00,-0x1448488e4de25cf07bf69935fb53e5fe14dfa52b9c0,0xac9dcc5b0be232b46ba42b38dbbde2b536583c840,-0x3d4e782cfbcc459b58492c3d435f96a0c9e57300,0xd12ef9dc37fab4b15b18fb21fbae0356be0100,-0x16910f13a03752c5bad1bc13bee990567cec0,0xe67865d39b5f63e67e06df741d4ea1bf40,-0x1a255227db3b73202db42b1688000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 24 50 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 50 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 55 indices rho q8 m8 8 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 55 indices rho q8 m8 8 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x1]
def r9 : List ℤ := raw_ints% [-0x1497b6140ecae2340d4c400000,-0x1d89adfbdd7a99a8fd0a940000,-0x1423eeb43e35575a6b088c0000,-0x8b04cbe62174b5583ae653000,-0x2a9b11d3a1656847066a1b400,-0x9df9d627029b54226b8bc500,-0x1cc46dfa035348c21b21f7c0,-0x4390786cd3eb840d1b04ac0,-0x8231c7f93b288d3158af70,-0xd06813b033b2925c11830,-0x11786929902340b7e0574,-0x13bf0c171248426e1a24,-0x12dec185613645e3b21,-0xf43992e078a3a80a8,-0xa71104352e34f246,-0x6059f8499082f34,-0x2e979a45c070ae,-0x12bb9e98b4060,-0x62fbce17b4c,-0x1a62d9958c,-0x588fd3d9,-0xe0e688,-0x19222,-0x19c]
def m9 : List ℤ := raw_ints% [0x0,-0xb8e2c7704e6a1ee577129fc00d2044515a4a248d2c4000,0x1776d949d32b0b50aeb3c7599a55be9674f5b4fbf16eb000,-0x1726525d7873b4e808eb334413341ce62591e403204fc5000,0xec8ca9f2371cf0db2e1960b727356e70e8333e0ae261c5c00,-0x6decbd9250d9eaa90ff90854a6b63f78afc0f7eed7b7310400,0x279d045d35a8333487e595c3c460527a5ddc5d02ae0e55af800,-0xb85681fe7901183b429cf8e74238e4a18c32e2d4e63f6c58800,0x2c765f744b93fbe884fd96a180ba0838cf87e841277053ef3300,-0x911eecab77735d35d8d81741844fa84ef7ecf2775d78901a9500,0x19683dde4ee1aa25a9118d06dab7c6e9181a3abe3f21164effe00,-0x3dc65ead6cd798dbd315c7062160f114f7454a815bf9b807ba200,0x8386a00e5204f503573617c4e83a9f4cf5ed1910d154ef7556900,-0xf6f12132ad44254714d3f0c821362b5d06a5e49d954401dc0df00,0x19b23235d18df7b86ce5c155b54b80540cab9e66dfc2f9f6092400,-0x261b493d9e18146302fe07599280451319010d152de615f08a5c00,0x32835cbfea5c7189740875b7d9cf755284cd2aa6f506586eef3ac0,-0x3c04390b83300f52f2b52ced85cec487f4af7cd1399e3db829e740,0x400bfaac4f2ace4501fca7ef62d628fe759c2aba05127815451980,-0x3d7a8511c96cb34d2c5f58c5bb9093f86e2de2a4621f93c07d2e80,0x3521bab692e2fc263e4a94b85acbe8b2cd998211c03fa34579b540,-0x295bf7b3ce1ead0215d52e4730a768ee558493e990824a30d564c0,0x1cff3ef026a4f211425fc8b72f8699f4b1704a43602c8910ded900,-0x124cf6a6b91e034f650d207a28181f6e7db09bdb907c569f2d4700,0xa62f3932fcb2d92cfa34fde151fdfb9b6316a04ec71b40ccfaec0,-0x54b0ad08bec1dea71ae0ba69489b8cd1e12cdce33f80b7eb8cb40,0x26acdf0addb241116194a219ef56ef0e26d1ec13f65efb993f480,-0xfc92c755049a66cc4f5dcc960e990b966c822f103b0ea3c5f380,0x5bd89967fb409249ef208700a486b0ab56ac1853239458e47740,-0x1da3c880127a7dafd13c8b5e6c35f2374f1d70ec3a9cdc981ac0,0x872d76b1a0b855cf08c35bb6a3f11aa764c10a3d9a616203a00,-0x21d79b7db495d3f0244df5c8f29bb0fe36042d189a5f99fc600,0x7643084476e5dd0a67fa1821d4b06aa1865bc57baa99f5ea40,-0x165a01f2176613112b354c63f518d5ae8d933f9c421883bbc0,0x39eca78ce4f978e86bac24f55456fd5a6da5ae758bcc69280,-0x7f224390cf0218dc3eb5209d003c370d24a412a6b4468580,0xe8f0027625e50847b3786d12ad787e9ecadd9d8e186ddc0,-0x15df938bbfbb808f5e7d8b8a66224cb00f0354ec2521040,0x1a595b53e5ff6d58063ba8b8fdd6b7b4ef5c8951620100,-0x18b9ba32d9a368d0912cf61b51e437d4428eb9509df00,0x1166d995b5e73a6218cec6e0d2c4362133f5fa61b940,-0x8b9b80e7297425ea7e70888a1ce9f3e420a5b17cc0,0x2e61c8c16303b2bd34ac996f73129b09f93748180,-0x92a2407184caf9bd5ca7699da11f169439f9680,0xe7b85e0c3d55b4461b7b420fdadd7f56b70c0,-0x8569f7fa96ef6b99b23b54a0f6bd227cd40,0xd6742f9e142963a7df098ce0c0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 24 52 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 52 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 55 indices rho q9 m9 9 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 55 indices rho q9 m9 9 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x19c,0x1]
def r10 : List ℤ := raw_ints% [0x2124290847ce840bc566b7000000,0x2f74fc4b44628469c32fb9f00000,0x204c4a7c18405dfbdb44b6bc0000,0xde79793b19f47e64581a24d4000,0x44068be4b19dbf1cf617dd88000,0xfb9463898e1ba4e2f4ae4f5800,0x2dae272836576dc4413f1ef400,0x6af03aef84d9d3f8f5c965540,0xcd4f164e4df68afa990a0d80,0x14744632fff80dab916a3dd0,0x1b4d612b33c509bc8d9ea80,0x1eaff0e2886a23807ffa7c,0x1d228eb13750a598b64b8,0x1762de6dbe3689cbc13f,0xfd9bc997b23b861060,0x909fbb547626fbe0a,0x44f65ccdd39a8330,0x1b3c79d03dd5bd2,0x8c91aed6e2a80,0x2447823e9044,0x742a324ed8,0x111ed3007,0x1af4260,0x15f0e]
def m10 : List ℤ := raw_ints% [0x0,0x16637626997ed9bdc96b41584196e845d9eefa6d185bc000,-0x2d05b9ddffa0341b35d6644326736f3b3ef914c45d6a75000,0x2bfac64095b605070bc981e5aa4f83b55c5eb31680c2133000,-0x1bcd93ea69af4bb0eaacb3e231ced9cb4b0a3f9469c69184400,0xcc94c662b92d75b87d6989ccc01dd739f69df3cb932d411dc00,-0x48f1551bff4c1380df58d91afae2db4e18b800f35e194a2a9000,0x14fbee1bcf82850b3d51101025b98cc443851bc40a8c36c2eb000,-0x5014716954ffd94484e46c161e2ced30a5b7ae42ea9a5e3f38500,0x10262ad1bcaab2faf9933a977222550e18143d2178e48929537300,-0x2cb4d61eb7cbdd4bbd3d997a3ca62eb05146ca9c53e393f312dc00,0x6b638433a3afdbdf5337e0b0d1d8edd1249032c7e01e0c01b47400,-0xe1cf6707465cfa4885e2d0b0ed321ffbd59c82e88cbc1847490500,0x1a28edbff4c02c9368dd94443eb0ffefb740fb2627a40e47ca66300,-0x2afb7c4dafff74c2b8272d677fe3fad3e46d2d314811fffce199000,0x3ee13008fff585b4107777948168b74f0a11c41fd3d7d3a4725d000,-0x5230649bb789ee4f8d59a686f73c80a4fbd35b154c63f44bffcb940,0x603edf0395c3a0d90c4c2e2ac029569c0ee41af2069223dc5d084c0,-0x652e2b5040bf68ceade62371f655d1e1f42f61281b296ab55d1a700,0x5fa0bf75291e7e489cb06ddbd8698740394664df162902d38f79d00,-0x5153b260f6e7dafccdcdc67425798407e508cd3d929e63972680c40,0x3e42ab7aa4f5d91fd8846e020f93fb51c331f7d717dd557983455c0,-0x2ae6c92d1e02635c07c893b762e0a3b2e06b9f1e841fdd505382c00,0x1a97b9cd2c07338bd6c7d8e3b794da199f690c965f35aa4a6ef2c00,-0xecfe605cd1bde53fded6121816cfd7e4743400643cd89aed348840,0x766f0303fd270b08f30918035ded36b28caf8cf9097c799d7f95c0,-0x34fd2e4be068746d2b4a78105be5118b4f32416319693f5fe56b00,0x152b5bdc87ae5c6ca490596d8670733a73d52e7bf72ec57c54a100,-0x786d83454e1852a1c9df30bb5979918fc3e6db0c605ba20413740,0x25f43657d1c007c93e9fdbaaf1928c4580720fe9a5dac66f27ac0,-0xa8d36b21934ef7dca553ed64133f903da408d93e2b1af8d10000,0x2929fede8a53800a80f2286906d26cb83e9934f14df1ddd87000,-0x8bdef678c94ff9b1c207064f8d9d717b35c6ca5609467e82bc0,0x19a87e5c0c440961b9d5bbbe1a7f753d10059e9592ea099de40,-0x4067b03c27d5699548514c9a1d76a2c4f3b0815fb78338cd00,0x8898be83872b2c27a9031511d864815effb48d12caef10f00,-0xf1319fad6e24c0ea230ebd6222a420b661192648acb4c0c0,0x15c22b50a4daab7f57053244a2e73f9de5b59ddfbed9d540,-0x191692f23e92a3452e733ab8f1ba9f8efdc93b15402f400,0x166faded99dca06011a31638880a35bd6f80bea6562400,-0xef86f425e298b88b5929e17de334efcc9e6ede909dc0,0x7125856778bc5aadd07418b5bd8f90212732f314440,-0x2323f5bffac0886385c18fd770b985dc0a699db500,0x66dcb938deaab68ec5c77068ed128fb5daf0cf00,-0x94b9d850ccb450511a87ea24438cfd620b22c0,0x4d354d0df0cf8fe31469b474b2ea9b14ab40,-0x6de75314b799166620ada023200000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 24 54 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 54 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 55 indices rho q10 m10 10 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 55 indices rho q10 m10 10 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x15f0e,-0x19c,0x1]
def r11 : List ℤ := raw_ints% [-0x1c3d22f17560fb3dbd1445eb800000,-0x28603eead02966df0e69f0c9180000,-0x1b6ee943e3e2272b55ef62b1b80000,-0xbc9e692becf0d32625e0b8f9ca000,-0x398e7872e8c2e906b155bb0569800,-0xd461c78ae79b40e7fbf506e74600,-0x2677512444ad43ab3adc603c7480,-0x59cbe491491e0a12ecaef026280,-0xabda5c38af70388ed1eecdd2e0,-0x110f5274ac5a541c0937af1520,-0x16adc8628ce6b6f025ced7888,-0x195f2ff39817cd3118a5f678,-0x17f574764d0fa504d8ccf32,-0x131c5bcd698786cadc9378,-0xcdb6994585383f6d06c5,-0x7446e3c025c23fce2c8,-0x36da6d23752bdcfce8,-0x1560df17e93289b10,-0x6c803b400f06b9e,-0x1b6601b31f4248,-0x552f48f3a3ae,-0xc0b3c5b518,-0x11d2ba5ed,-0xd28338]
def m11 : List ℤ := raw_ints% [0x0,-0x2b60b4eac965c5dfb63fce9aff146207563f05335f31c4000,0x566813402d70678ca298440c7fec99b34b3103b16111c2b000,-0x5396d3d6c3d3d5e23f95f32f2d5e2319a87110286a7efa25000,0x3452070cf1e1f30e2fe156c5aca035580660aaeba4c29ea8dc00,-0x17d153cb9968611c5a58eb2addee8128c85082b08ffe0b8a88400,0x86765894a4d62654273389063f2903ff631f89e42e4497d975800,-0x26451cbf8f6b778bce3e965cfe93a8c8119de67ad467d209662800,0x90734b407829d8f62f61fffe642b69337961a642a00c760f1a3300,-0x1ccda9dd376f097b56847ebd0a3013c2268817498e61d87c8e09500,0x4ed1a29f8707b74996ec206dc1e6f796f43d211954b038210199600,-0xbb163468ce6f6cfb284f5e669e580a0c6fd574af62c7986da2c4a00,0x1849954a76d91b47f1b104af3c48354f24b6c983fef5d517ad7a7900,-0x2c742f7b70e0349b3aad8976a03c0999db0a1e587c3f71e1fdf2cf00,0x48189ab4f030314a36f734e9fd59d5cbb4c4eee2862774a7cd177400,-0x681072b5912c45fb6ac82e886391a54f633c11ff0f35b6a8d8530c00,0x86260fb6f67318a3985bb5bae84d693fe96c728141020f688d26aac0,-0x9adb9a2c20dc1153e569e9723d35da4002af9312a46072ec2d4f3740,0xa067474e52b9c4e7e32ae9f7b0cb6ef077429eec6ca32fff6b8c7780,-0x954ae17ecdcd913e83f506efba6cef8ba97abad40671fc0114eb2080,0x7cf6429afec76fb8d2b4e2426e054752113917a3fb78bfa2eb17c940,-0x5e1929c7140f671c774a96f1fcf6752fdde236e830120670341610c0,0x3fbc67694837ea5f38911d6d081971f0d73c76ef9e5cbffb29426d00,-0x26ce96271b40c922256e7b52254f7d37fcef51d1a2f091f45eb3f300,0x15375bf5a06f225a46ab34aa7e331cb4a7fd34c320bf39d89312e6c0,-0xa65e4e9917673c36935e63a9db83887194158a4a94bf1eda8cd3340,0x48ef3a5e51d371b4fd4fec39c05dd8338636cf29354bb70dc7c7e80,-0x1c8598bec9eaf555f297a16f4978a1a2f14b815a04b7cc38f3ef980,0x9ea7306afa81acfef3c2a5317df5dda34c48cc85bd91498959b340,-0x30d5347813e5c1e15007f633421ab419f68bd82c687d28c2cb3ec0,0xd3dc98a23be49a71102e19af34616dd53f26e8c06f14e3b4bc200,-0x324f42e9e63d6b606ef575f8b7772a289372824d1dc11f95c3e00,0xa63681c9f9d6bd01fe07ebf6f0a53d70c2f661d216deeb21ea40,-0x1d9758864aa0ca4e0e61e8f5e9e0ce07826fff03f898185ebbc0,0x47ef85969173517a2bac636e609d1ce8c0dafd94f7e2b99c480,-0x93679c441724c797a0f390c2cf9a1b27cb342c75d60bc3c380,0xfac6f32d677d33fb237b05c07d2931534e61fdcba779ba9c0,-0x15ba45b8f6179124b9932c0622ac3e190fbefb5e3fee4c440,0x17f89f0d86b1a1fdf18c8d61ba5e94d5c7be2f3dfeb87500,-0x146bdaa208eb4a548de7fb354298a99bd1c1a9866a52b00,0xce961729ab154a1c511c168bfe8e40d5ef1d695fe1140,-0x5be15cd99f5123ef5344d297654973f7f7003b0ec4c0,0x1aa8838c68d32e02f7a423ce68597214f0570738f80,-0x4833ffd2296dcc45ee908d6e6771d28c0c1ecf880,0x5f76a08c58f59b88cd6679bc227b258e373c4c0,-0x2cab183f417531583bc7b0b0bbab311ffd940,0x384e7d383abd7d1ba5259cb93000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 24 56 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 56 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 55 indices rho q11 m11 11 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 55 indices rho q11 m11 11 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0xd28338,0x15f0e,-0x19c,0x1]
def r12 : List ℤ := raw_ints% [0x10ef017fd03a629cd506bd6d6e000000,0x182dd77fd02a9f40d4ec0ce620e00000,0x10676c5bf2aadb28ab1f25b0b9880000,0x709a428bec911059fec36aa9bfa8000,0x224c6ce279aa20e9a844fb54adec000,0x7e4f038c0e661a81d927dbf60b8000,0x16d37f3ecad11ac6c5844085ce2c00,0x3527af6c3b949df82413c06142580,0x6572d3b5963d2de26b18280a4e00,0xa0a28d3bd6ea78368e5fa3007a0,0xd4cc58cf4bd1f7ad556fe8f040,0xed1fa79bea4487df00ee88758,0xdee73ddf1d3e246819978740,0xb0def4e898281bbce2b298e,0x76453be72899bccf178e98,0x425fc73672503a09a59db,0x1f0bd01b82ea1ff60200,0xbf9db7e4508d0e9c18,0x3c0473805e09e3ab0,0xeeaae1024c5ab82,0x2d703828660680,0x64079d3a6412,0x8e90819cb8,0x63ac3c73]
def m12 : List ℤ := raw_ints% [0x0,0x540b5e86e6352f61711ba04c4e377dee371a1a1388706bc000,-0xa5ddfc2c32988d7d524fab33b606afe653e600a2e6b6f935000,0x9ef13381d75e6a23b01fa6d8218f36a023c24dbc2d2d5c493000,-0x6285bb5d6672ec7f01b046a3d12753d3f94ba336b9afa4c3cc400,0x2c67af3d5c86fdcc00f6fb4cc4bc726a416a8fe89c580015a95c00,-0xf822fb853985d801369e415de342ed268465e305c94b8e06307000,0x45e2cfb0a2cdc77e941b4c136e2bc2868b21205432ef40824b5d000,-0x104f520c024c47506fd84271e2402f2575fa6bfba8fe7d5f5de94500,0x33763981a800722c3793999a09b65db828b069556befbabde877b300,-0x8b3a6829bcd1931e7f19d7821b060dd627519e882a998b34aec9d400,0x146a073daba4b3b7cc71b636df466783800ade99818b35ee62a24bc00,-0x29e4da4ec84dcb2814cf9e7c32a3e7eaf2686e00e9f1db824dd69e500,0x4bbb6e04e627413d6175e2c4c5599a287ea85a193f37e141af7510300,-0x794258a57c9d914886bf1010b2c53b1dde7a9b7e662755aabe500b000,0xacb9b9bbaa6940ea55b9b435ba7fad0e71e87971e9d84ae519c0e3000,-0xdba2aa01f417981b01cca253dc0c88bb79e3567ca09ad32d8be4b3940,0xf9fb171a9922b39952bb8a2aef037ad76f15c3aabad27ebc8e57704c0,-0xff2b385b18df447ffe90c49cba89f6f9c9b5d438fe7fddf1f925c1d00,0xe9ea86633549b81f71687c3685d53c7440d048a2951ae61b3eb58b700,-0xc0bc00c8bf48b5e10ee9cd1314fac031ef7824dc47fc99597f73e0440,0x8ec6a37ec685498f6df3610d2e385ae9ee49ccf4db26df086d0ebbdc0,-0x5f12ef54e1078bd810394de3c90537ff255d3450364d71e0020daa400,0x38de9b1150e5bb9ab975c9ea0f1fda3c7abf4d7addaafb95dbb589400,-0x1e854d297cdf73074f7df2d4c941a86b68026164a91d6cf8a5ed5bc40,0xeabd6e86221d1177278dd2d43d115bcdc41616e211c6cd18e2f361c0,-0x64d77f94e5f712aef1115ecc9961e84ba584ca09c32f0f76345af900,0x269ad0926b7fb8062a0eaa49c333b2422319bff1fd4f275b8b8d4300,-0xd1fc10fa8ce49e4b90fed9069f7373de44a96c9c709aa5a2ae0cb40,0x3f1fe85c286e2df7ef4fc9d517d0fcfeed2a599c966e925c0a746c0,-0x10b1e15d226c2e35e39502935ac769df1ee7783da55eee340fa0000,0x3dc664042bdc4ab9183f7c4330c192d73965df1980d948ccdc3000,-0xc66e4343a6899a6d40e3f87551d90a0a4ee1a727b72bb3b4b33c0,0x22483d6bd72548cc3be3d3f5c6e6fe54c0d18e2597087b5dcd640,-0x50b39ad5f8805b5373dda1e3d53916380102a323bed017889f00,0x9fbe0d789bc1b8fcee59a01a0d22bdd73fd5dcae8b1ba3b2d00,-0x105c95a1ec4d2c4f9eb54600746287ae88f29f26a51e96a20c0,0x15c707e25996a070c9b35c8c0325b0f72a1146954e66e69540,-0x16fb13e326e1179eb1d1ff5c9d91f614ed4a94db2fcdc7c00,0x12a440bad0c3efcf524ebc4fa93670819873a74750597c00,-0xb29ada73405b854d4a5b91dadbc79c1ecb04b2d41b61c0,0x4abf57cb19827210a2470db78faf63785b997fde48040,-0x143f6593b1462b389266da40287d0a236bd058b8e700,0x32b5f811d4af7903ca71a71da2b12d5100efe6ad00,-0x3d46e8381e091aa1dfffa27b9f759ea6a12796c0,0x19d5c42150c4d65736aeb2943927e5e4b4d740,-0x1cd6c37890ee9751db17649788000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 24 58 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 58 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 55 indices rho q12 m12 12 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 55 indices rho q12 m12 12 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r13 : List ℤ := raw_ints% [-0x8048634e605e4444e453c7ad840c00000,-0xb6f2ec155af2d7634a6b5d229027c0000,-0x7bf445e0d6ebb8bd9beba893f86040000,-0x3519ec20d1557710cd4ad6ee2952c9000,-0x102607e1c184b24a723311d2254d95c00,-0x3b5d202c560987f9cfb1dc0d2316bf00,-0xab50248fd390b1474866353e547cb40,-0x18e11ba34884ff2fc3a815d76e86840,-0x2f5e5d8f20d662cc8481301d20e9d0,-0x4acd4985085b1bfadd753df9ecf90,-0x62caf2490908abbd24e5909d567c,-0x6db5e59e1ee41fa422ec505df6c,-0x66bb74dadb7ab38ec1defb46ab,-0x51282048c086d34420d4105b8,-0x35fe0c33ed494cfd86a627dc,-0x1e1f4a79869ed56e1fa7f0c,-0xdfdfd14251c95b74b9ab2,-0x55a6bdb8c230b6ffefa0,-0x1a902116c4fb33a7500,-0x685bd7a33839f3204,-0x1391df9f552e8f8b,-0x2a41a15f48edd8,-0x3ab613536ab0,-0x27a65ce584]
def m13 : List ℤ := raw_ints% [0x0,-0xa2d607255e070bcccb258693d78b83fd8ac29285d859d0c4000,0x13e783b795bd34340e322957fbd3ff840c8b4d302acf710d6b000,-0x12e5aadf41a9d55eaef4cd18b32fde6d05099fbdb6ee4516e85000,0xb9a4b2f2d5529be59e25d70315d601fc07a1a4553762b9f5815c00,-0x52dbd0584c46ca10015f67f670a938ca1245fedbab6fd3adcf80400,0x1ca66ea17c545e15eae6fd162e3229f48380abfef9fed6f46deab800,-0x7fc8d8755ed5b2234eeba395be94330ef95d76d01b1ca981c5c7c800,0x1d822f99424da8191c9eef3898a5e02a89e4a9dc62516acdc8ec53300,-0x5c19c72a93d6ed516bcfbee25ea9f52866159ff8e7a96e1c575ab9500,0xf6677df25e1e34251fbc3595fa0496309b69ef5b4c8398adfb3d6ee00,-0x23b7123a8901061b29b4d2a21576b4dd976cc0de105e879feda2bf3200,0x486e14f9aed2fab304c0d21c623ef10e6259a37c8dd0d6a134cf768900,-0x81570c49f3b5bbd3032b375a564f4fd698183a6993f0c76dd3c8a2bf00,0xcc7e9d6c7984c9a43a3d51f2151ebb6f8467ff66efc66144614c834400,-0x11f833175da2b1c64e77092c5bd4e11a6126d96b5b652d9c02404e63c00,0x168b26ce1a44ebf2d70ae257c0a55a44f0cb5b590e3d562634c975b1ac0,-0x194d671eb855019bb90c4e15aa57537a1fe74cef825847bee300e34c740,0x1974d39fee0ee7f7e9b8a29d861869ab634859bfad0610c74f218cb8580,-0x16fd04ef4f3899562e4a9025f11bc9b5a0075975fb21cb94c0f830ce280,0x12a5e85b0d8667ac566be5e983c5e6a291e32fccad17a660805aaac9d40,-0xd97927321123817719e6362db4ed933852e7136eda708601364d183cc0,0x8e63951bad1fb3c559f3754bb0b6727bf611f92d3dfc966fa484c86100,-0x53af226252e26f91a141d4b7975f5d8e2daf45e9d95c15f5e7bade3f00,0x2c17ab51a0a3e34ee67d2285e5ee377328cdcade53bbedb78941435ec0,-0x14ca72ff7a2f607a4375e41e6e5f355bf436e8d4878e3a5ab678179b40,0x8c0c17c5ff534709aa889de91fc25296ce6535ab8628e8c1202525880,-0x347cf21f425971d1f6f6bc2f0cc9c847d399eff695c0b2b53360c2f80,0x11731a64d2b8ff73e3288abc24e96b4391035452993a6a201fa91ef40,-0x51f972e9320d86de7a12cce9acb89dfa2eb4495ad3d374d2cd53a2c0,0x15255bdabe52efadb93bc091a35f0a3dbdc7899427167b39ecc20a00,-0x4c335b44b5fb766d3a320c1ba392f87a50ac62108bf4e0d626df600,0xedf7163ecc00b8bc6216a86f97642adb796af05754cf8085ef6a40,-0x27e4915ddb768c0c6acd2bdb23b654a39d9748902b48a73de5fbc0,0x5aecbfc058e777cbcba11a940fba518fae907efc913f79a814680,-0xadd33af322665b501b83eb595c68f1d9d4173e326298c00b3180,0x11256dde1a4ab4800b861fe22e3764a7d0a822d166297d5f35c0,-0x15e7d600b1e26c5e0e47ab1bc1916e69fed0d68b17f4b477840,0x161a29a7c602b8c2cb7078c9884a3363cde9727b9ebc5b4900,-0x11107b5fb9f29e309c493040fb80a43ccf03fe70ec44e1700,0x9ac3d0070db9ad31b8165ce0caae7c52fe3f91a2406a940,-0x3ce9b4f639f8c27c884cf2b46f0d0c42e89cbedacc8cc0,0xf65392d8e4a04e06adab079eddf56ffdfde071778d80,-0x23a22c1154fcb2f5f5e40beb21070234aa73cd3ea80,0x275529e77ceb3d69a34595a9b955b39b5b2f898c0,-0xef01ae3b345bba324e3a5dbe332efaa7132540,0xec431ad444ae7f2d0dc955ccc0000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 24 60 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 60 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 55 indices rho q13 m13 13 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 55 indices rho q13 m13 13 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r14 : List ℤ := raw_ints% [0x3307e961b05cf29182ee72ba31091000000,0x48b26f9f113689f29e9d280c74797900000,0x31320ca75549c63b5ea318c65fca1b40000,0x150c1e58c1bb1f99d26576ef3242a18c000,0x66435ce9916baae4fa31fb8fb5ac384000,0x177558761d8077a66a178f59c9f2713800,0x43941709c5b511a978cdbcf69c60bc000,0x9cb9a6699600ebeaabc1a8be497c7fc0,0x129c1f430c9e582c16ccac45fc013d80,0x1d516443e9b6ed436c14530e6527ef0,0x269e526f06392d3c92b82571a4a840,0x2ac24f16e2272f6a337cc4028fa14,0x27e7ce028b77d865f00b5d0f5ed8,0x1f67c40768ab018ac2eec64f9f5,0x14cda74831c699b618238ab900,0xb8c715dcf9535d13729a1554,0x5556b104cb611238f6c4770,0x206e1d257cc7225089b4ce,0x9fa450fd5102ecccee80,0x26d36b185e3d05752f0,0x7324285cc099ad278,0xf50ae2af3c0ed95,0x14e40c97a71a00,0xdc60e802aa0]
def m14 : List ℤ := raw_ints% [0x0,0x13b7eadd8662da6dcc998b4be719e4fbb3cd8fbe3532e047bc000,-0x26399f4a61e473e661cee6e05263f97744067d62a69493adff5000,0x23f69170c29404d731a201e03d81c45473e1a15277daf61e7ef3000,-0x15e06b6dfd66245371d3754e49778f6afb6ac07718392635946d4400,0x9abe4260092b64a8b3624326f78d84279f7415b4fac2d8ba996cdc00,-0x34fbc6d63c2306a9612b3be4d6ea92232fdcf9d23213d4b9dd1f55000,0xe9f2196aa9006e68276196db633053d1b5f58040081a67bede785f000,-0x357776f84578db7cdf5b7f1a183cace4bc2b8a787359ffa95fdb710500,0xa51b7a07b8cffe406c5d8da17b254860c556769d645311ba53892ff300,-0x1b4e66c1da71592d07d551785596d3c05751a93713f472f5a719d028c00,0x3e9d2c73d35630e0e236cc1d590b6bedbd991382973cc3d87ebf5854400,-0x7d81de9fbeb202dc556c3ae568db2352a0b42bc410e7b7027a01af24500,0xdd701f79d66a68e31b10a5cd923a0bf768480dcbfd6ad6dde3b1cde2300,-0x159c719cc1e92b875de9ea6dd83ee65fb1526c4dada2b7fd942ad4bcd000,0x1dfeff63c7f3805fcb18c040f3afd3b363c843f5e52d29d88337e9259000,-0x252237fc342531b366819aa866d1098992be1a1e34a59bdfac4a45bb3940,0x291b632e38b0b1fd479243033f11b1e6970b52586807ea0f4e50099984c0,-0x28c50d0de996ead8318cf57694078dd1a97213a442511ecc5164584cc300,0x2446358c220593107fcf5b9f6862c62c14678f317e063a941094115e2100,-0x1cf9826bf5651063dc667779241d1ceee8faedb823fec1d2b35b72f25c40,0x14c835bb565723e6167697bf541d93fff3e079fde3bdae0970b164f545c0,-0xd617c051ab11f5dd549d5f3d40f8cb5c97bfdb65372d421d7895b87dc00,0x7ba4b96335954e1fb9257783b8f164c84498d15926dc8d5cabc6f803c00,-0x3ff73dc45c645bdf0184d7a93d30fc563474876fe3aa89eeec885a3d040,0x1d96d40c11c507a5d79f61a7b5c7bad641d6684dd472ced669ee647cdc0,-0xc3584131d937a64292167587c25c4c2723821adf06048a2e60c57b7700,0x47ae46d6afff048c3fa312fd7c88b9b7769f6dfce041154090d1287500,-0x174e0d8d0e5c8674d5f2020274ce1d5ab60bb26cd3a8e265c2d4c4df40,0x6aeed13822bee3833ab52005a13c5136ae0b326ae3da95641d83c12c0,-0x1ae78d5c3a12736fbbefef939f68ad54476a97f77421acbe1385d0000,0x5e6a8101d4400d4ddac1bdf9f5e436f39c5cf20d9b6bd499a4e7f000,-0x11ea32eab2f258254ecdf17d695529349bd72397f290b14037057bc0,0x2e9f51829c1de84924832f3875109409f86ba2d0b606895f8d50e40,-0x66df14e37d5795f90860d0b583840e0872bac32c128d39038a8100,0xbde79b2eede1f9eae2fcf3f4fc286523032add3d3fec745e8bb00,-0x120929e7ab337aa77d050a83ce7713c090f09430f24676d40e0c0,0x161c4d01538ff4239c438509f4212a11fba0f03b6ed7267f7540,-0x1552a20aef6eb48a3b77da54444bca41973c0c3a38b0a254400,0xfa97805d4682863c403615e12f53dd61e82324f3c42469400,-0x86651a72cf449f1b6d3b03f7c4c1d9d8fcbc35dd691485c0,0x31b7ba6e082b008f0369d3fc16f89c0d649a15ca88bdc40,-0xbb7b604025b01172e23e640918dbb113e33fcd0c72900,0x190cb00b4a0a53cdeed4a3730348a14d55c4d0e9fb00,-0x193ef70a8512395e177511324c10da5b05d2e64ac0,0x8a27553a9ec5ac16074b7c7dba304d5c8ee4340,-0x78f079081151a12499e0830b200000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 24 62 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 62 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 55 indices rho q14 m14 14 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 55 indices rho q14 m14 14 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r15 : List ℤ := raw_ints% [-0x11ba2c07381a3ef2db5a2e43c56d228000000,-0x193a78016375174c5e9acf628e0d253800000,-0x110dce6d8ff706d50828ea1313904b7f00000,-0x74999e3990db90bcf742b4a48224f76a0000,-0x235ca22ffb9ce16c3977c563a4a4827fc000,-0x819a4b174ab6aabf82e2519741af974e000,-0x174c5cb70712aa473845ad1c302f56f2000,-0x35f07975b3b40d918cd298083c14667800,-0x6648761d0aff7627678aac028f2b98640,-0xa0cc35903eef73df2923a2a202a5c080,-0xd35011836b15cdf9a45aeab10af9190,-0xe95c2c6c38946e4fbe651f1875e640,-0xd926dffd513edf92bb636e50bae8c,-0xaa561f242970a2123cdabdc4ea28,-0x706a19611acff7b51faadca56cb,-0x3e2423276a5f036f437a40fe80,-0x1c8f7a4f4c30baa107552a00c,-0xacae8adf6f45038395e6490,-0x34c7c77503296533ca7032,-0xcbcc0cfaed8b50521700,-0x256cb06f1cde7701270,-0x4ec0e83f38b0eaa88,-0x69efdb11f21c02b,-0x44a05eaa6d280]
def m15 : List ℤ := raw_ints% [0x0,-0x2634570d345f8734bc697de30fc22ba7ac5e46808712928afc4000,0x496ca2caa73da23939529605994500d8fdc6af9f1f90da549eab000,-0x44786086da327f672c6942c93e8fcc148aaff87c3d3d12cf7d3e5000,0x29461771606fc070ee039536ffd4e6fea218adad3d24403aa8d55dc00,-0x1213ba622cc9954b3e093b5ef5b0bb0de8b74b632dcb1b91623f7b8400,0x6215fea4d35821c2edc76f7b52405048ff9505e48347e1b6a7d4911800,-0x1acd645832828b3635bba922d86e282f61b4505a5484bf74edb2b3e6800,0x610449240136a3a24ef10c7e1c0c6f4def5db858d5ba933e10b60543300,-0x12879108072c3f1835dc80cc1d462b6b99c50572c49993dcd07214569500,0x308195a813aa132c337239f507929e997786da649af0ba5fc6177a2b0600,-0x6dfeebb8f8342187140896e9e041478de0475e9555204192be1e1bcd5a00,0xd9f74b49db85d7be74a5d8880c967ea55555807e6fd41cd2f907a1469900,-0x17c08b6f5c935de293338473c322970e55823e048dc6669ef862c0c76af00,0x24a327fe95ff3eaae7a6f2cb6f7927ae2b66101ebd940d60c10fbc90a9400,-0x32361f2536965648a5195f45ed182a5d36fdbaa005cef7cc71a2009b5ec00,0x3d590e94aceb9848716b943db5424a650e949518e4a3478af896c85ee8ac0,-0x42fe4207ce915225df013144fa5370a86d3e09b24e74d8235144721645740,0x4182b46d226f38950f3b3c1f777da18a809942c385f949365aa4e027e0380,-0x396fcb30ba7715df42a841538c278c310986b2d47eae496b92be50c85b480,0x2d2ea79ce1d1f3379e6601b6ac4620dfafc37733a920a6d2a57c1eee87140,-0x1fe50c6467063243359ee715322bde498ef46ca6ee4b1a8453e55aee968c0,0x14327e6020e54e005ef75cbe855ff9b1ba967e15d65c3302c2680eadc3500,-0xb76a65649ddcd100af0d0e0e207ca4a8e1a87f4a8ca75d4cdfcb1494ab00,0x5d2db188e8853fe4685fb9e3f3335676990c62d881da1f8c53755cad96c0,-0x2a49cd0661f71a6dafa4d72b1ea5c06097c53f9ef477cb6c1badb4f64340,0x111a5780952af4394fb60b8c37c7c21b8b036a4ac377cae0b9160f93c280,-0x6251636d19cba9990040696067d32dea6b58267cf29e8b7f7c4d8d25580,0x1f4309ce19898c29270e5ff7abf54f7bff4f00342a4148123363932eb40,-0x8c1b654e25617d6c1d974daf0efcec72d1e82b0b449199e6bc2ec046c0,0x2261e771ce6cb45782b98c46e632e79f15ecbcc2072a7d70416dca1200,-0x757f9b151223f4c47b7d807b6420bbe3b8fd33b6e7a753acbca5dee00,0x15ac14f3d4a7b9ea47c581f240a41d34e291078cffff4cdaf41e76a40,-0x36b770f853642b3e199925121663d4f520d8ce6ced211dc06c4fbbc0,0x74dc6e88fbd22c6d42cac7000181ee285cb732fe9e9e35d29655880,-0xd0468786721e78c58075c5bf39cd6af6786b222c053d7737a98f80,0x130a55390c511817473a058d32ceb090a7b24b7a7578c34c8d41c0,-0x16643d81c95e471c24fa92fdb3059a30d9b8c6480058d3557ac40,0x14a1b26946e59e0ab5279f4455566c039df162e8d2c384c5fd00,-0xe693bd2b1d31d4a988c08895066d9d97995200396a24252300,0x74f12cf949d981ee08b6fec9084a2009c44f08abff5380140,-0x28a3ce4d30cdae2828b913d2c555718c5e4c14190fe994c0,0x8ed2d865b1b9b69b976992dfdd9b9956b7361e07333b80,-0x119d9d569008c69a511de8f49ff3c6b3830f7601eac80,0x1034051488372d1d3fdeb9e63ddfdf4fb3ae0e32cc0,-0x4fd56f3235553de22070107963c9dcc7e0edb140,0x3de3e85e0854c0f8d2a88d663000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 24 64 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 64 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 55 indices rho q15 m15 15 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 55 indices rho q15 m15 15 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r16 : List ℤ := raw_ints% [0x58532cc8ad939de8348961e55ee0b2a0000000,0x7d95903d4ef245d7e7781751dbde588a000000,0x54ceed7a9e2bc3c40b833977a3a47cca800000,0x24337faa070d235b60922d0945115e9c080000,0xaf747ca6f432e219b8ba79d24c9a1b7180000,0x282389501d3fad6bccbbe8c97007da8fcc000,0x734985354f07379b583aa92c22709b428000,0x10a7ed78c2d4d78febf8aa6f9bcc7887c000,0x1f87c0c8c8405726cb8041aede57a7b2000,0x3179abf640606dbc77972ee9a3e2c9f1c0,0x40e21710c0a9be9b3db75b436995ca180,0x477cdd977957923fe064936330fc4870,0x425a16e4ffe2d064232ef313d4a6440,0x33e5db4f51f8c316ce711b3323b574,0x2223cb95fce672478b4a2959d88d8,0x12cda03a100fb4e3b55dd53c6735,0x89b32c4dcd153d345ade83af00,0x33c9ab539f63874568d130ff4,0xfbdfe560eec5de731976f70,0x3c653b0779d4d1d44505ce,0xb01dbc9a975f30c95680,0x16f46ba7f7a33512190,0x1e8ad845080347c78,0x138551fd9d711d5]
def m16 : List ℤ := raw_ints% [0x0,0x4a0568a9957915f62d0c63e7ee883494ddf6a89905b3fbed48bc000,-0x8d10d7f865fb0d6f3b39393a6d07e2f80265ea0e47307fe4836b5000,0x826a0cd0fea961292247b0d89a4bcbfbc0ad8459ee76aaa6917a53000,-0x4deaf5347202b72448af844525ad0e75548391208bf22ef9a43269c400,0x21d0e051c8c7ec3895276b30960cc6e9858d959a160d9c6545567045c00,-0xb5c4a536cb83ba2e3be5ccd2cfdcb4a2fe54beb10ed19dd3e29a8693000,0x3130c9c74a1c380e155be2b09d4da07fbdf357076c647418c2c53c0f1000,-0xb04a6b0b70d83f8ebd4e0aa36a4dbc45d5defd028d5fa43eb9f1eb22c500,0x21538f48d27e0875592995fd35f95078ab39a4291a5827f6a55bb74763300,-0x565270bb5b38c5e6785a270a1114c5356a539486e1a51aa7f3af555b10400,0xc19f25a819657d7e4f783dc10fcf5d38a13dd7e9b62e79731396cbd1a0c00,-0x17b5ee6cc9f60f83115129d04605de23f0990cc83d32f4fa8230a05b482500,0x28dc6ac4e4ec328d418f73c0319ea8efd015321bef444906a575d078edc300,-0x3e45607520331e79bcf6f0e80360cf4236caa541ffde89163a8e1cbac1f000,0x544818f248fe09f80122bc7f218acb514114e20931b84495072fd89a47f000,-0x65a5e79605e74bda0b80f316e63921a2da72d11dbcfef3625ff7124becb940,0x6d84ac9e89f7d3ca070c493234a5c9a15f37d5378fa6b0faf10a9bd5f084c0,-0x699b96ad1b20fe402169e929c03325829df2a4633c850ede2239ddfc649900,0x5b416371a3bb0609e1f45e104753fcd58332440cda1d77472654e4d464db00,-0x46b4e1b0a276e049e7024a1b7d5305be980032b0f4898a77723ad619749440,0x31216990282df1bc008e9fbf0c8afd16866babd327c3f9ebaed7e44a34edc0,-0x1e9a4ea8f5d48ce7b8ac1fae28b18c73383b4d865db413cdee685c6ef0d400,0x1112808e40e65783ed4c0d3358f483608d2b3fcab74c9df06a900bc9a92400,-0x88484567381aee94005caf11cd71df8fe3521d9cc0ddcce3456a42beac440,0x3cb02405c9b8847a44863a7df6bd0bc1282adecd49ff6e968e38e162159c0,-0x180f3bd5ff414a6587a47ae42969c2810ac82331a252f95ed897a3bbee500,0x876e4739b85dec6c3d04a4a8b3e9fee39c5d5eb0b699e55009ec71a03700,-0x2a1ddf592abba8750e59dfa8477ea3cf0e795c809afe5c06769b92dcf340,0xb85e5fa8cb16354b9e69578f1846cc2ce169173d12e4d33ea6c9958dec0,-0x2c20fe6d5bdf64a0fb67c88a54462d5456e68338d3c0e55c27b38900000,0x92d9d21b1c92f649750b9e50ae13d1e5483ddf58bc457ebadcb98db000,-0x1a53ffa0935e18faa600f2e47022481e5f924e45ae96c87d40d48b03c0,0x407ad2b5a1aacb25073609385b14e5c037ef69ce07b8f44f27bb40640,-0x85473fd4b508e15af1af158c549ebb441ea9956577ab412886ff7300,0xe5481ce9c55dc3e367f879bf03db0f9766f81c652e678dd94fab900,-0x142bde5dcff6f2b346f1d4a3780fb6f6cfea8b5aa4440c2e25780c0,0x16bfa7e3028b857ae992189517ed1e6c7659a6219c99d80d847540,-0x1404f1c8731ddd9a72d9c7ba89eb77f5e333cca1f3cd3a4824c00,0xd4ab4004a33aae696ccc9b5472003f85dee65f5305f6cac6c00,-0x65f3095a23eabaecfe30fbe88ed053badfc869c52375a409c0,0x2143d53445d00316f0ec605598e3432c3eb468217083ed840,-0x6ce455e728eb5cea5dc501de921cf91aadaafbd870a7b00,0xc6448555d1ec75efff40583a3f9dc4451ec433b8eb900,-0xa660347069d90a2add08f007b4d49bc63076803bec0,0x2e1e8814748da16972c75e103544ee5ecc46cef40,-0x1fa9e5218817b87f6a4d9c8a88000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 24 66 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 66 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 55 indices rho q16 m16 16 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 55 indices rho q16 m16 16 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r17 : List ℤ := raw_ints% [-0x191fbed7cba2caf7d11b73ce4c377ae0b1400000,-0x23b14b41c0770b84495251dc271addd701240000,-0x1814e7cb2da376d5ac2e60a40bea51dade7c0000,-0xa44f238c62d906e1c9472dd92544d5357e0f000,-0x31b7f0893fed4c3381624534b40a659b176c400,-0xb5c5bcd0e54b124026c4f73b1627857f47e900,-0x2096be407a3a19289a0706e5edc198fdfa22c0,-0x4b39f1d146473e84dccbefd98d11618a271c0,-0x8e3008f933cfc9fc2b969b608eb5c0f8a830,-0xdebc63b271f368fb57006fc4754c2192ff0,-0x1238f492a0ec505fe33be316040728098c4,-0x1409462f05e56ea930026b7f0ea993c4f4,-0x128df450604ae9a030c068f63854d8555,-0xe79d499d244f7aca53e9f9e61f35208,-0x97ee6f413821c4f4bf57352962dc12,-0x5369e4e10c2890cfd6c0b35acfae4,-0x260aa1f4e2372c58e4f547356df6,-0xe3fb14f23efae68860f1a09660,-0x44fa2c32faf937af6388e5534,-0x10735ffe3128a816ab4106bc,-0x2fabbbb03f9f93dde364dd,-0x62aea02f46ab28169968,-0x8226a7a87f98ef2ede,-0x524e19e9bcf81cec]
def m17 : List ℤ := raw_ints% [0x0,-0x8f6a7ac8919a9a8cf74801915e27e5e06e0de6a87b0cb81bbcec4000,0x10f138ffed13f3be42f8c252e68e1643d3f38c2565ebcae6fcc9feb000,-0xf87fcbcff1383db20fc7db3cce51e1261d274f8ca627b967f184e45000,0x932f57a7b1ebf35cdbeb9877b871a4dcb0885903fc3d173c750a0465c00,-0x3f4f22520439342a608a121eb03821ef819ac6552b0f689e655dc8430400,0x1512f2b02629fe874a9cba180e0bd48cd3467203cc7eb3157a68699327800,-0x5a639c6d4eb8fc5aa2621f72cb43e3512d2230fb6591b30783149efa20800,0x140ca7437357f29c0c5c626b9b65d4aaa2180eeb6cef64535e1dba2a873300,-0x3c0905a2ecece12d2db8a432d0a6cc69b1c50b5e7f88212431784ce81d9500,0x99e513e3d046d55b0c43ff9df2e49a9787c91e58835ec54e6350c574bfde00,-0x155804b91e2f1ac5b672a5212eeadc61fc50d6cb4e4ea11836dc8fbbcecc200,0x295baabff6fe6d9a2f90c5ffad58ba2257a4817b7745c4ab9a2f144d9e2a900,-0x4675833e2956b98decf36f3dee4b93f50f0f3b8eb8a710e64d86655d7a29f00,0x6a1b9590bc049ac223d27222e20a201e58cedfe50d0ed9c04721659662d6400,-0x8dda649837e2e354e64446db218b6d825e31c44a1e8c07297c66b72e3a21c00,0xa8e83fa4cf4e121f708d6249e3e7a22f144f659ba9ba49014a4c2cf1304fac0,-0xb39516023d3585f8f6c6853017c6c251a722433d063c69ec45a59d2cbc8e740,0xaacb15eef6c639501311d2e190e7af203cd0ab09d7690c4e1be129f1cb87180,-0x9179460c33bd91496c47e42f0e8399888a8f14deb73b72cad4d6c37cd611680,0x6f09b268b9379a215258bef13d8fe3e6bdc5b96fe297c2aea58c371a6d94540,-0x4bf4bf719614adab8256e6dbd77c323f9b337c5a554c973512fbaa77a3a94c0,0x2e8b3b23119fa4378d51151dc7ecefc19d642ed66b31511c53bebd50839e900,-0x198628aaa8b4feca71deae17f786bf23768e5b3fb7eb11ce6db83f0f5933700,0xc81ecd9049593c35dcc4d5697f59d6e1b734aacbaeeebc93d4b30082b68ec0,-0x5772d5a65257d2a3728f2ef82dd92e3145e0337ea7b762b7bab387291f2b40,0x21fc73a69156287aed930792f26197dc99410903a1f11db8023232e7fd3c80,-0xbb5652b5329cea480ef9e3fd9494338314d1ca27e07e9d24334e733bceb80,0x38fb27c59eae26002ae5093bc3f4e7948a95e00a3470103d7772c5de5a740,-0xf3a4fcbaf833ce9478e14cbc824cc2aeb159dc36cdef392af354ceb32ac0,0x38e0ce7624c6da5cb0b16cbd33f2d1e8d49078b4a29ce769923091bfda00,-0xb84e366ec7f39af375b6b96380fc2869750b33e8766b748627109e02600,0x201db0adbe9fb29ec4f4802d3cea7ccc54d602c3439306f7b7bffbfea40,-0x4c4a0a6fbaa0c0cc49e8939719131fa510e262105845f4983157e2fbc0,0x98962d90465de58c3e201496a727dea4b89b5fc89e154ae3b1c037a80,-0xfd53763232e1fd0fabb682dfb326be022af8ee3d39bc4eab13915d80,0x1571223707d57e6b59904385f68f510626f6f4fe9e1f9568b995cdc0,-0x172eb94cf04553c1a80b669cd5c75fdb0370d58fa7f9ffddfc26040,0x137a49e69367e12219b4034fceac7ce34b693bc63dcfbee5989100,-0xc498f0b72457657f3dd5e3c950b49f3c6b625caa84f8b3a24f00,0x5909a83d01525cae98b30c84ccfe5e51324b2dc4685aae31940,-0x1b434b8ccd7134ed0cc4a9600e2594f97105d0ad66ce31dcc0,0x53153ac01b3bf7d9e442036800b6b88497e26d903e8e1980,-0x8b81b6dd6fb032221c39eba5c5f3b6adf1c20db62dbe80,0x6ac2b1b97b52da02c7048e43c2de06e099c0bfa480c0,-0x1aa287e4a7b673e6aca3c58722ad209307645b7d40,0x1031f88cc80e382914b211248c0000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 24 68 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 68 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 55 indices rho q17 m17 17 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 55 indices rho q17 m17 17 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r18 : List ℤ := raw_ints% [0x69ee0a184e98afb90eecf2d3c9d5a4e994b000000,0x965fcec41fdcd2154e944b82c2586eaed3f300000,0x655f6271af957b1ff2791aa4138b349642fec0000,0x2b30a45b89e0ac083826bfd33724edbe3780c4000,0xd0e5c21b71edfc75cd5e9b735fed165b54e10000,0x2faeb9accda4056b0ce29db36feace3794eed800,0x889ec40391a0aca6657ab03f9399efc3d217c00,0x13af778a5186304171aeee49c14938502b7c640,0x25280b496a6fa6148bfd7f1d5e8e294ccf8980,0x3a1dea8d4f7e81e9cb84ba4648fdcda2ee410,0x4bf29c05e2563d8ba664a493c79619199300,0x535a8cb9877a6c42dff950b414a68da866c,0x4d08761bafb0fe30140bb1c1994c313438,0x3bf6fefee34200f8566d15588575d8b8b,0x273c96d7b907545a02adf3df45a77b60,0x157b4fbe2ca991d37471ed5155077fe,0x9c42806a88f42e498a1ebc7f60c30,0x3a525c84fec7e970001b3accf48a,0x11932c31b06da30477fceae1700,0x42c1be703955ec0f9e46e211c,0xc06d3b671408fe787b58a58,0x18be4a8a398884da180d83,0x20660e89c0efa6492a60,0x14501fb6cddca5b092]
def m18 : List ℤ := raw_ints% [0x0,0x115de4de49a1b8b711f1b8309a66d4d62d53aeee66e68a4b5be09bc000,-0x2090364671b470d87e0206bdaafc4a7a0885228a16a91286e16b5d75000,0x1d9b1e3e62e6f57cea426f21abc5f0701ed46a99c0e3b9cba03d046b3000,-0x116320ec65c29035364105056b6bbde7d1fc60c94eaba59c79226bf124400,0x769eaf4afc986ced69d355d8b4186a8e23444016828a65ee282df9a2fdc00,-0x2721b545708944cee7a5b0b4b5843faa84a0565d613e234289206f2d641000,0xa64a4bfc6fb4c71a117c3c2f8d32656c686d13a9461335ae219ea795393000,-0x2488a8cd0bde92ddad1ed520f059a08ef150eea5ead93023c67fe44aa9e8500,0x6c51e120f307b4b928219c70fc28645db357beb9c5746b23306b79895727300,-0x112d91dc3cd1d5fff2d28382dd4b21fc93333b0625818973c603d747afdb3c00,0x25b804220ac6962834806f72b469e696afea02e33f1052a017d2c77e65cd1400,-0x484b5b76048ce23a165079cf9a9e7ba189f99c5100e3cbeff7f8f64656cb8500,0x79c74b07158f53c995944bc99f5f7bd303c4e1200e6e12570fa1dfc957d7e300,-0xb5417348ea6bf1d2030c79c3b6116b4e99c6eee0960dee2e13e238cd7aec1000,0xef636e056f27d8ff125daa1f57927f21ec98786af66c00407bd43c176c995000,-0x11977c3cb84748b890686c16d2833a89ab52815f0f526db5b9a85ddbab4d7b940,0x1275aa6f401533cd94cb6832bb819d36404be21dbe693edccee077d43b1c604c0,-0x11516412bb1972383a1547460c43c410bcfa579b15ad4e58b9653e2db87831f00,0xe8ac40c1f6ee5a6cf81a2ca88e76650541c5d43a19a4e5c9674abed595f96500,-0xaef9f71399d1821a6dc8f37cf1bbb0f243d6c8f8265f97c9a9a9244d54ecac40,0x75d981bc01ddf4006aaa4934fb2fd3c3cb0b2e6cae450e34558d40310658b5c0,-0x470d2ab160668cb328808aecbec4e5381be3c1ea23c0e98ecf89a2d3ab248c00,0x264e4d4c02bedc632154914f39376567ffd8a5384932521782379a59c8a44c00,-0x12703b9253223b85aa4c37a2ebced8152496f54e944332ccbe0e9754af709840,0x7e83aeba357badc5a6deb583d1c648a4b23c35773a0e2ce7fa3e97ce8e405c0,-0x303445934673276cae4c854cce8d534165e159109a136893be098fdcba5c300,0x10435450c3dd789936d806901358a2fe3d94cbd49aaf939fda5c2bd62400900,-0x4d699375c4f5d0533419562314dff9483d1652d23ea77479aeed1429e70740,0x14351fde29ef5cb5323d47bd3fe430a4e4195d383248119c9e657e7cbdaac0,-0x499d76829d3cc0ba2b0db07dc783ee793ca8f9b46895e7e621fdd05010000,0xe843124cd300a17f968088a98fc1db77944d79929ce470a59b3bc5ff7000,-0x27556ef859984b30edc3d9cb680f0f5f886d6c859d75a806b33ee95fcbc0,0x5a9d1a9c7d969b144392e71a469abd5b3053dedbe10838d7169933bbe40,-0xaf586fb17309860db721672146a75241347c55433e6e04081ba657f500,0x118e150f8cd1e2921b12c2db4e3f10f637b1805834255398f31604a700,-0x16ddf91ba396b39130aa218656e5bdceb44fe41796fbd8c199de200c0,0x17b1c97f7dd6600c9173b56d17b9c182941ffe993b1cba5ac7039540,-0x12ffeacbac3b5555ccd705651857b77d01bf8d44afe47ce47729400,0xb621cef7ecfaaa8ee51e1627f0a8626e72bc780f0ea3f10cc0400,-0x4de44c3d16fc042d977712270a12dbfc139c4d157e47f9e7edc0,0x165eb10af7168db2d678cc3d1eeb0190deda566f09429e57440,-0x3f6ede364277b2d0691f251f3364d612ec706dfccb1fc5d00,0x622e665862b60df8acbe6bda3363f554b91c6a2352f6700,-0x447f5a47bb70c9565b6f85dba07053231f1772a25f2c0,0xf60b402fe794a46eee66a5f0390fabf738a71cdb40,-0x8480605c70e21fd29a5f5fbb200000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 24 70 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 70 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 55 indices rho q18 m18 18 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 55 indices rho q18 m18 18 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r19 : List ℤ := raw_ints% [-0x1a24c2f8ae395a25c6b0a1a230dc223f9417c800000,-0x25161662e31c769dc38a7618db303290a607d680000,-0x18fb6627c93476e708a348593b8f6e50e39e0a80000,-0xaa283441abc7a31d7b7fccb06e89f3d012c6c96000,-0x336427cf2deae473fb5e1259aaac3033af3fec6800,-0xbb8109dec89379d72789f72840d16be9811455a00,-0x218aad08daf75541899ce38a34c9cb5b0ed847380,-0x4d3d028dc9eb6972cefd706cf5c308c1ba8d2580,-0x919abd650b6b2382c17a9f07c40c08b6da947a0,-0xe36db2cc06a6e7addfcf2eb1bf3df0d2e141e0,-0x128c2179d539492a7d6c74501a9bde7e713a18,-0x145287bcaeb6b69ab95854067ae82c485ce88,-0x12bf4849eb89b253c7a15aad68e6e4632d86,-0xe90685712d2c353c884fe7f903bbcbe498,-0x9822e67e7b96a801eb635a46967b76331,-0x53166059ecca76928e75a3e3f74dc4f8,-0x25ab837e74d497a10c9959482bf9d70,-0xe042d9e0213dab7aaea9623b4e190,-0x43581f2bc8d927f3e3bdb90f1106,-0xfeca6a3ffe8fdfb2f217fd6db8,-0x2db1eeb46114318c50aa4ab52,-0x5d860a7317207558c9856b8,-0x79b88d7f3b7a16f6b9849,-0x4bc6b706f67b89da088]
def m19 : List ℤ := raw_ints% [0x0,-0x21a5eb6eaea955e2b2c454de2b273c5ef7d222ede75eabf202032dc4000,0x3e997ddad63d72c0311c07c1f251af0ed880d08e9a21ff8719138512b000,-0x38752d0c90fd661d68752493c87529bad89de8af49b129d4079c48b5a5000,0x20e213d25a7983eae209532bcea92199b11711c6483cf52b253efc8132dc00,-0xde6d8897549a6577edcef3dde50e35708dcd39baa70daf438c36959d2e8400,0x48bbc4ef77771d20ddfa33ce716fefded2fb0ec3fd06646d1a74814dce6d800,-0x13248f7f0a3325cbd8e97d098b5e868cfc1bbe7b9db2f0763a79b923e71aa800,0x42a986c98f6fb2b643d5d5c9e0512c3c1bac06b8d022564dd7a912ccc88e3300,-0xc3bddefc24839f1cda80415492e3bdd8bc194d1121f4f7612155b731e7c09500,0x1ebb7dac0f72a16a902ec56a822df24711d399c4dc755b07fe56530709ccb7600,-0x42c8f4ab2f295f8cd4aaf118a04acf9cd30884fbe32d2f219b35afb0d55376a00,0x7ea336a9e63a9ecee66474f14076e30fc7cd27bb5ce74a5a670e9982f9aaeb900,-0xd2f53e0a4ee50e99300cb0cf939eab744ad4963b3ae34bbb0f0dccfb28c728f00,0x1366311006d6b2e534c9d37dd2f6c917cfaa399f372b02449b3f9260871cb3b400,-0x1950cdda726868c699159b75e633741433d0f91217809d59791f5440244282cc00,0x1d65a160635bba237f96b190e2058d947691f428db3ec53a974595860d21ea6ac0,-0x1e732b963036a0b629688f151e3814d0e46bf6250821436d0057a0a99ae8d27740,0x1c2eeb9ad68cb1028bcccf5d4e8ec3a1764e1155bb7684a19b1abe97503e9e4f80,-0x1755ab7e0055503afc1e9c1dc9b065c60e18396a38b0fb25f3b027c17fcdbf8880,0x114aba6cb3f0a00ba1d8c9632e9ff967cbf01b1dadae6b3e0375e43be814e41940,-0xb77ee56fcf4d5b54a18e4d01512c4ad82039741fae77f0c49015c771def62c0c0,0x6cdc18b46159caaa3f4bbf663a3868e548761cc75542dd0ce05d82ed442cf7d00,-0x39b47343d080cb0b590c1e3729433d3e52b0506c94f3577839abc93f9fe53e300,0x1b495e727c1ce01a6735ed3c065085faedede97b31bfd6d68914db420f80d46c0,-0xb7c0ff8361ad11e66c4a3003f79dcddebca1e5eea274664c635a746a814f5340,0x44a4ff12f13fdd644249f979ce749d1f34a7eaf1d83965b965fab40653a04680,-0x16ae42680f786211b25ffd273dee8c7d950255d8776617297f587f3922367180,0x69996ce6dcf08fcb1a43d30cb52e72828c2dc808e6070836556a363be982340,-0x1aece447692d09b73a6c8775362bcdaea51af982cb3013ad8bad1abd3aa4ec0,0x5faa172a51f8a4aa3c4d05c69587aa2ef5504ff3cf72d825edb54e5e536200,-0x125df10d83175a288b76fbcc21a218d3892574c79ec93d479cd8c5b3949e00,0x305cdb73905775ed0f76b5f44fb59b4da9842e9e12fc82de0618c4992ea40,-0x6c0974d909c39c037a1e9ac252e7ecfdcaa60d119fe82a5bbb3fa5f9bbc0,0xca3b320f53f85a496a886906fcdaec4b0dd24e5bcafea951f5595522c80,-0x1387f312b1f5b54f763663b2814f9c37212ba28812cbaff2e3a05881b80,0x1876c60ca31685d83b25452095130760ddcad8ceaad3ac7ac03f89d9c0,-0x18495954f21ca2cd06a50bf7c76b0a16e5dd4caee905171f52d2a9440,0x1294406843cd3b4f190d5fc72891d6d9dfade67b5b209aca45150500,-0xa91350f4653e68eb5aa74a0ef97252aa7edddfeb7414a3236b9b00,0x443f8e00546f0a98d699f5f9e57a6dbbcf57ce2df9f7a7072f140,-0x125ff78b4ccc80050b1b3656ba013017f098cec33cddd9ae64c0,0x307596e88dd09ea6a911b6793b71c12f9a08e7a85dbc66a780,-0x451bdeab324b5a08993129e3ffed476f723e36b1d556a080,0x2bf10585585ff21e182d7c938700e0c29c827dcee494c0,-0x8e036744113fae0bfc2543a3b8eba2c4230b7688940,0x43bcb43458d7fecdc3d17af73000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 24 72 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 72 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 55 indices rho q19 m19 19 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 55 indices rho q19 m19 19 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r20 : List ℤ := raw_ints% [0x6186e67b663352e10c705d6dba361169b9f882000000,0x8a41ed09b0babf57ef2c3999eb135971d08ca2200000,0x5d11309469d51914c9c7f9229f4471dec1af8cf80000,0x27969a73d8efc55ef4dcd216a58aa033ab4873198000,0xbf2586a8ab20841d207571bb95791976254339e4000,0x2b8c8f6e011c0f2da20d600f56330f9af210e744000,0x7c85faca27a550a9f497519507304335a2845e4400,0x11e71a8295187f127f0325898548ac51e47e9b4280,0x21b5d502f2f26f74f66b72396a4d1e8a401e60e00,0x3496976d99e29b01d67a74dd4cfce107a57991e0,0x44868bb442a78acc7b2ad0f524aa664a6276bc0,0x4af8a549a01a0c10da0af08a22408b52132d08,0x450bffdb5730b617f40029dd1d7a9658e8b80,0x358b28e13e5cca098879c873fd3e53402fba,0x22e3427f7e9ec04ac10276c84e8493d55d8,0x1302f7cedf700f8bddb8110a3fe8b0392f,0x8992ebfa4f5bd00a4016040957687280,0x330c9ca36a761144d6cf04fed305190,0xf486fd0b3fa99011f0d89c1f846b0,0x399f6a5e004329b0cb6f73c668da,0xa4b416e864dd20be91fcb485c0,0x14f9900b86aa1ce35ead85aee,0x1b28c1cf19b12ea4db001f8,0x10ceb9197f1fc10bde057]
def m20 : List ℤ := raw_ints% [0x0,0x41317826726816673a5c646e739c04f8002723acf0476d24e3e628abc000,-0x785d4aa667b8c38a4177811664aee4d9467773a6054f68e510b261d435000,0x6bb47d10e3e33f4d2adb09464d934aeeb6ca1c69a17c5875a90635c4c13000,-0x3e39b1a6611e70798f18a3c2b76e12c995c402490a486e52fd5ea5a2ac6c400,0x1a1674a22ad7d86ce8daf2da49b81f59ccc49e6b0a23009979f5012afc0f5c00,-0x87519f5f109ff6f0b3ced0c0526fe53012f9fb3c263d0d1482310dc7451df000,0x234c9a7b5f1219ae19eadcb8850c16db406244007b63ed6497d02f491550c5000,-0x79ccbdc2d2de5fe853111fa5efc746766678089aeacfc881c26d5bb91f2244500,0x162427eb6a07297cd81560653af895efd1c80c556283e9421d7a00ac931184b300,-0x37137ab0ab940f3a72b5a69cafb22c7cdece73acd3a70fa6a4999039e8e67f3400,0x767945df4b003e0d773a223b148194e48ddaa7c5e2f7dea1152a58b691d7f05c00,-0xde4a5d87bbce4448c061c81c4260ed4e5d406b9fcf98874b02618fcbe3e4246500,0x16e446e2270ba31343a9c64da8c095cb3b4353f2a365ad64c34093544d920348300,-0x214cdb91d329c613ffa75f50dbc926802b6e1434ed06e7fe285cf108c0a39773000,0x2af21902c85d3365ca01491e3f945353bfa172ab6241a52b552ac2b7eb4c59db000,-0x314284d8326368aa26019715c33a7c32213e04565ecd1da267fe866dd5154343940,0x325fef85a90d06f714b7f151639d1f7551cfa1a20261f005b8ebc0f90c8170a04c0,-0x2e01a01fd84ed835ce923c0b807e40f916621b41a58afcf4832a70c93ce4e9dd500,0x25905a85566353cc572bdf80c4bc3ce7987279956d1e6ccaa7eb8a0c3ae3c6a3f00,-0x1b6ef2d16b466ef18053073e31e18c45bd2001fac98f1cf7d9819bf3384fc9ca440,0x11eb402947d606d5a5156055c19cbfc94f633abfeeba3d56604312a966b0f2e9dc0,-0xa7631db466914ebbe3b1e3f347814f0293306d986142e0448ab601bd0264ba0400,0x57400ea359a46983237a147a79ea350f7aca3c6cb191ffd942ec3f5f1389eab400,-0x2888c896289c2aabcbd33d7adb28f62bd62fb4e75c08665fa02c8e219ce3db4c40,0x10bed18f4608ff843d3ac2a9788397a38b301f0069d2803e949f3ad2da4419d1c0,-0x6223442b2f83d783f60362cfec9d9dac6e80055c429b6919d82676764223e9100,0x1fc1cfc63f92e485c8ead87d815e801a16602bc3428dc0d7f27046419f9cd6b00,-0x90a092eca2763af2aa801b3dc5cb497023009c3b0668957e7e38c30fb85b1b40,0x240537364f04e0f5e9cce8c0fd35e58b7b09ace15132df19b1edcfdebb5a76c0,-0x7cd02a3cf95246eadaf843378a21e30d5f50135e6d68bb4b61bcecee0be0000,0x1754855752aac3218aff0192d219600478a1e353e682e8288908e6f43af3000,-0x3bb138c88ee799482561aabfa434beb7830a4f8315c6d2416cdd397997d3c0,0x81499593d397a0ef4510558ecb2d48086a8df650a8110330ce50a03a03640,-0xea10307121aca2ff80c8ebd9785af07105963ebe73bf167a5776dcb68700,0x15cd31b96f9b1dbfba9a414380113157b56a1bf4125cb3a73cab80d00500,-0x1a40883ee8ce57089531d6d54b2ded4ba47e8713f18ea716576332260c0,0x18f611df89ad8a5a575fed51197181dbc494849156f303d74d42dad540,-0x1235e9e329f5363829009933fa0caa3a216517614e6438049d30d1c00,0x9d420b48da4dc0445546585414ee8291c456d1118d8a92735fe5c00,-0x3be2facbccee0806a2de987507904e6afa646fdecd4e198c2e31c0,0xf1bb988a38867d5f1856466233a33d9036983170f7e402f1b040,-0x250a30158ad0a3276e6dc3b2e20304adaa56d202ed6dd484f00,0x30a6b6b856750ed765c83ae11be6f142883449af3484c8500,-0x1c2f26aff5dade52f292361b24863295c29b6951348e6c0,0x51f1d996f63d12900f6cb299a59f56f20069802a0740,-0x229eb722c0b6d6a8db56d2ef88000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 24 74 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 74 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 55 indices rho q20 m20 20 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 55 indices rho q20 m20 20 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r21 : List ℤ := raw_ints% [-0x15a1c5974afad45aa698eb807baa6d72009e7ce9c00000,-0x1ea5c96c6a576f570d2a6770b568ae5dd62c8b964c0000,-0x149de4681553c39f3f24ffeb17b6ddddb9a0a9c5740000,-0x8c37dee30b6395de24bccaca73315fe77da5db16b5000,-0x2a482196cb82a660d9afcbf1b8e7de61cc159cf5aac00,-0x9a0091f627d520c3478e75017c4823fd61f91641b300,-0x1b7f52d8254335cc8322a3a6dcc03ae9ab23cb9ef240,-0x3f310a70c590f69ed9c3f47ecf9bd6448b22fb32340,-0x76dcd0945f517040ca649587a8ecc21cf565ba5c90,-0xb936e5aa3b758f83c079afbc0e2f123b2a3532a50,-0xf10b818c4882f5a5aa1ebbe9c65d4c536c5cc78c,-0x1075c387ea5a7c25cbb80e53d8c9e6fbabba69fc,-0xf23057a0c0b975952fb36187f776c27fc5cf9f,-0xbb8101a70dc6fff9b1b4b5bef9a92be7b6118,-0x79f463292e47c663c9d4a61e96afd371ada8,-0x425396d17ea4e6ae55e17ce74de1578e97c,-0x1dee9d62ece07a3c387b1da596513de37a,-0xb14784dfd253ef3e5ce00d35187b02a0,-0x34ee1d897877e6d78dc08bd974940a8,-0xc6f6e71eea9f3900d69f6cbb7c474,-0x236c4934561e9621ff99773a084f,-0x47e646e68760dd1b2165bdf6b8,-0x5cb0b339a91bf99bdbcf73ec,-0x391289382b4de44d6e1d14]
def m21 : List ℤ := raw_ints% [0x0,-0x7e4fd8ca7da9ab6801130295fffe49a0804bd51f118a6377798deeccc4000,0xe77a11656d252ea0e72fc7f6cd8e0a886e237342e84f3da0868f2b8b26b000,-0xcd8c5c8f0d36aea2a4beba87769a79d21b67720ac12011d4cf7c0017f205000,0x75d14220b82b527d0550f397c3fd1e6700ccdb39a2404a17a4a2998a90fb5c00,-0x30fe29cab3d1199259dafae2d039f53b489dc70b3ada9c23c68ddf9adb05e0400,0xfbfeefd69e04eed27abf391b5006a4ced571be68edad09bd85a7906fbae463800,-0x412a57f2e851cace1df92ebe203188a2c20ce53a8b96f05c981f74661b51504800,0xded61f95627d30404bfad449c2a1bf3dfaa7298b94655d87acc4bf32da7e593300,-0x2821d8f2319f5f3dfb5d9490d3fc6936251f6a95ed4a39cce136098d1ee410f9500,0x62de8f825949a9fb9e3c43f9c012604bd55981723f304eb1499a44ccfa7bb23ce00,-0xd28f452c9543bf1225fb1c6dd802d09fe13ed67964af625d22d2357ffe5aae75200,0x186fd86e20382114dfdd906f85a1ca8c9a3a17852a8e434e73f5ddd364de453ec900,-0x27d53d56aa922b42e6c09a6fa24c66750805232a1d158615b5538e9106c915927f00,0x394c8b93f1f32037ed9b3bcd1569da9ffa15191a1589a00a73b4486400dc2aa58400,-0x490a26ffe1ec799029da26ec3aac8e11682a159491b055349a633fecbeee43effc00,0x52c4909f5b09af6a6de1174857fa0b73ef3d40afac2d1678af688c982e31f20adac0,-0x5393b1b0cb1263577495c53b7780bc49bf4f8a636dd0d641172977acccc9b6050740,0x4b53eb4a3b661e7535736461f6b7273fc3c13c2b0b7498be5e4901434ab18d9b1d80,-0x3ca9576a870c10516f387156526b62db138bdd037b130957980f2d8359e4dc298a80,0x2baa9e3f5c7b5caff301e59d99ee2dfebbd035337b02d2e50e05e980fa5836e9ed40,-0x1c17ef884f49155567944fa6b2b08148aaee721b70b10efa0517082e3e6c9950ecc0,0x1024b35e8940bb6d5e4e4e9947f97990553ab85f09a7d701205730d855eed15af100,-0x84678d0902b83669b9f4ec5f13975d9e0ca57d6261b17964d5ab15473ea3bc0af00,0x3c7068c2b67aa4e419241eb74b5164437599259b4b87f570af6b9f07ac810e8bec0,-0x1882590d6dc087ea01932e7bcdebe0d5d355497868ae26802d4514c070fe9ffbb40,0x8cd8cd4bef276da11a46eeecc1e0f97f06ce6ed240c95db5bab63c21bfb9a66080,-0x2ca3cf98576f925b67006beefdf1f964207647bcafa1d4b4976f94375d21816780,0xc6dbff514b8e148e5fe8c1e46f3323f84b18811b84cdc4d1cac69167a892c5f40,-0x30608a0440fb4862a442bca468fe6ea7121d4d3116056e6b63dfe607abc53b2c0,0xa37a91b294e6523bab1e042a1ab7fcaba230760c3ca7ed053c62df98df54aa00,-0x1dbf91781cc0e4e8add6c809606872b15081b292f70814b5900638ae7afb5600,0x49f39fa18e4b831f6aed7e6628b4cb8422bf73b5cc62a29933f8fcb2fca6a40,-0x9b46ad205d576163d1003680742afb4db7c25f53e06b9e5fe9e25813f9fbc0,0x10fd5d8bf048db1607ba46b282977e89219d6a3c7b3c7b9a065015ef3fee80,-0x186a0046f0c013052f44e441e861cbb2aae30c657b1a872fa30b249eb4980,0x1c40ef47871a9e824f3c433982d3fc8be2264f0f34f19c52cf0a065e65c0,-0x19b8c410c39f108f15fe5d5cc9476e214ce731626939b13e32e230b4840,0x11e3b24a73a6943a6e904015fdca2deac3eecffcd4c2e6f03f4fcd5900,-0x9288947dc47aba9887cd243ddd6fd34bc2f7140808b28e3655970700,0x349f277c6888c607c7006f8b62e1c0521597cee257d8490211a8940,-0xc6f0ab7757522a563df0a4dab324d09b8db8930f322abddfc2cc0,0x1c5315e933f47013d94cb70b19247bda06de271734a2e5a36580,-0x2240a8e50d3bdcef9360c5c6eb66c9c8a15bd24b0f20f6d280,0x1213053ee674f76f7ed4745cad03b76e7d46de1ed54768c0,-0x2f453eb7ed0a0903da2d0711e0fd4363637364d60d540,0x11b097986c8c86dd49710c254c0000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 24 76 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 76 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 55 indices rho q21 m21 21 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 55 indices rho q21 m21 21 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r22 : List ℤ := raw_ints% [0x497453ef9d08683c939ef5f3c289f850037962d35000000,0x680297ae1f3d99a53a6f8850462c40632de4f12add00000,0x45ecfaf241ebf5941487bf95de5b25d767acbf0f0a40000,0x1db443fa23faf745859fce1903bd2c1a871174bf0e3c000,0x8f364d6d270b40fc1e00dacc95fc818b9e46a9fc9ac000,0x20938ed3ae955b2f7ac2d898d1c879516d6bd512e1b800,0x5cfd125deda8b9b96ba1d432c29fc3258916115f66800,0xd581a0253fc8bc06c06df9b2efe9e98684e96d1ea4c0,0x19137228b64739b95b033f8c894ceae6b18cc93a4180,0x2708765fc47fcccedc46303e9b81d8b738741b8f730,0x32bdc59415b5009e92606c390e9020048289985ac0,0x375ec340302f598f1daaf5c783941d85fe1d94144,0x32d9aa528dc629ae5293e0bbac8046782a19b6d8,0x274f7b2ea8730b996edd72af280d566a3722f81,0x1986d2947a4e56d8503fe073fdaff6d426bd80,0xddbbc0ebeb023c270e626148ab69c04d3648,0x63de7900c033edcdc6ebaec659dcc7bd570,0x24e37bd15037ae7cba9f6c3eb7f4f87a06,0xafcc5400fb65f3fc39fafff5a71d2000,0x2930f5de7c60aaf1dc78aa52ed46108,0x74fc6f9d7560006a888e704cc7078,0xeca71cb67b2d1f57889ad22d551,0x12fec46f5366c23c47b6c58180,0xba52fa1060e6bc1b17db4a4]
def m22 : List ℤ := raw_ints% [0x0,0xf4bab4085378bc198214d5029ffcaea6f892ecec31fc20b77b82feacbbc000,-0x1bd3e79222b508b692f92076995ea2ccad1e9354df6639fe3da59ce9d9af5000,0x1886c30d375e5396faec9e1695a0d7b20018fc72a026392b74cb173e659273000,-0xdf3347122960a66007901e4a4c2d56b8cb66cb6c2c92e3e7c1701ebd942e74400,0x5c13ce1938dd323268752950fc87de01ec0375cc06fe4378d15fd04869ac42dc00,-0x1d5b69cc9777ffdd1e683566b23047800f7933307a8115f55a032c6118f2c0ed000,0x786f66406b53d2be66e82a5ee4730414f9ac6b5b42763197eb2ca8715cfe5507000,-0x1983733ec25626f2c2756f4b1dc120bccf4fdd43465911d9da6490042adb32f40500,0x48d97d61f54662ffeaf6e7ae7a378cde267c687842bf683cecf9e2a3247e306cf300,-0xb1c77a000a2752c55d98c334c13be4ac15af9f269e83b5da00d5581d94d7b9aaec00,0x176e8ac58e1902676956fafb3c909224cb21e113ca55166c89824ed2b496370c5e400,-0x2b11a8369f3a45a2cc4b3ae7c9a36e3d5e6a11f650aa4351d8caad0cdede5ff7ac500,0x457696ab1ba3c27e271b11caec2f90ae188cea124beb75bea6b6ce5f4f48c9a3ba300,-0x62d342a5b067e91d50b4413fc3cf8e73d8c248256d35b6805f6dcc23c07611c9f5000,0x7c88d9c468e045fdb4b54110f1507ebe7ac08e53e89ea41d75a1934606dfd7ed91000,-0x8b70f9cc172113dac92ff947db69f78a5196e8d70c017844d3ee6594d744048da3940,0x8b0e336c4fffbc7e32211e99bd6042e297228a6e33e1b0d9da7effebd9690132484c0,-0x7bb454e26bff6263d98b4aba460a8a7f38b7c993358be4e2e37007e58c244d8fe3b00,0x62446f783030f0775e9e0f17698fbda94a17af11921357dd7a6b1b87a657f6fb1e900,-0x45bb37e5b27758fe79562267eac59f9cb627009e2dbbc972593f372fb315e9d667c40,0x2c31ae5d5dc79a3fd23b2dcac08e66bef32c6ff0871eba8702ed48de36ef0500ca5c0,-0x18ff686b70d003aeb313d8a8f973d213ca05180750503e2a747379e946b5492283c00,0xc9a644cacca4c28cac608ffe4236c2697fb443bc1ddb612568443b3686c5ba955c00,-0x5a7343ac9b7f889c030d62cb1749572e53713a00277a0b4d7f2bd9aaf028bef8e040,0x2401decfde031a81dd401b454dcbadc8cea11dc28d68bfad3e634e46960ac43cbdc0,-0xcae9e91bd7c53c982498d43a8823c5a23316bd8ded5a01667ccc19a0d4d0c2bcf00,0x3efd902c89c7806993cf8e6df21c18334a91bded8bd81020509668eefe84a79dd00,-0x1127c14081a3cc5c621b8b0dca0eb2315bc97ab00ac066b2ba2ec5e25015e292f40,0x413935ac2bf402d8ab50c29cab59436eec376ec3bddae5acb0144d6865de8f42c0,-0xd6f0e4256a2d420da42f3d2ec0cdc1a97ffca4ab26f817c049afedf7e73350000,0x26131599f92aed31e6725a6edeec126f28207cac5ce7dad59a2fe3d85e2aef000,-0x5bf3bbf56d6015fefff884b20fc3862aa441e0f945d08c27e33a771bda771bc0,0xbb24e90379bc926ea1e57d533c5c4e5040fe0aa68932299e6b2834e68ed6e40,-0x13cc1505d175e5a3720b61985e894cd5ecb87b665d7a6b759bfe0b54039a900,0x1b6cb1486ceaf0a9cee0730952761713a7d011b316a416680e7dd2842a5300,-0x1e7e7243bb239623b507c635f2bc07371f6f380c0ca50a05c75c19e6aa0c0,0x1a9268dcaa367a91de37640b7746d2813d3b8b44ea81cc8080f64e103540,-0x119c8a6a10ddcc350a798eca53f0af46f671675889bcbd3c01745e8e400,0x88c698f61058bf06f5d878f3f238c1a09006a23320e1e5804d69c7400,-0x2e4c204e9d67245c8bd88700e08c025b334a13d5b6e407a415ccd5c0,0xa3dc0165f7909c07f6a462697557f13093d90e2a8fadef7db58c40,-0x15ab3c329b6ac8cc57354ce560a14f62c306340c1a000dba5d100,0x181de18098e6051cc1c698a80a22f97eaf875453751f75a9300,-0xb96bb715135419cf11b58cc79321b70227189412d0409ac0,0x1b42c03d27df9c6e6268f772b4d4180809eb4fca007340,-0x90970911d64a9270222a3633200000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 24 78 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 78 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 55 indices rho q22 m22 22 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 55 indices rho q22 m22 22 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r23 : List ℤ := raw_ints% [-0xefce7005e4290c0071e345ca994d2ef6ddf92d61d9000000,-0x1536270921ac132e5481b19810ff1c5b8e27d15a1a1d00000,-0xe40a0061dca0190945ebb8081e45896c8162d7dd3be00000,-0x60cfbbcaf3f157c4b9aa119552684d96a021e0a25deec000,-0x1d2735fe000806f18b4ecb483d76e6acac17674865439000,-0x6a075518347e8aa746866952ca22b7e7dec7e7560737400,-0x12e6d1ff5026db92c48102295c4fe17ce486f39e9d3ff00,-0x2b5d0c9f2e2f5421b8fe2da27be25b87aaed1873487b00,-0x516a4467c081c48d6af97d1456ad442423946a4bc7f00,-0x7e9bb90e96573f5649d75b62f5941d45608d2aeafd40,-0xa469ea49a97db64cf285198443c5039f8c2c95e1b20,-0xb3358eb3689cb11e3fdf5631ce4d4339c037c2e650,-0xa460a2fa06552d1b3b0d75c6e67ec95a01bea2220,-0x7ee75365705f146ebd96e903681f9c22ac1506c8,-0x52490884b294c1a7eb51f6528fc0ab4f1538ef7,-0x2c99c6c12806b7718a7840768ca553d10b4d30,-0x140d841efa65d2f801789114d0234eb572114,-0x7647c28ecf2ed541a5a030bb6b6c84f9610,-0x2327937cb4bc8e087b200bb44dac0ded1a,-0x837accb8a48bbbc98f856fd80162db70,-0x1746c3f527c914583c209074eeba454,-0x2ef25e04e1f61c3e42aa82108cda8,-0x3c1745d7568699c14595c6c5347,-0x24b36a30bab9ac1d0c308ba50]
def m23 : List ℤ := raw_ints% [0x0,-0x1da29bcd021b9ec716c085cb515f99263819cab09a0d87f637f4dcd6eabc4000,0x35894ba9fcea2001c7d8127d3f4cec881a02c52802b6bf3b387a247895c3ab000,-0x2ed780acb9d5f0d95f397384ff3a82a7df02fac49f13f5d3e22f55abce76b65000,0x1a713a136216e5f36989f5f106a803497854efc73fdd18b922f8cd781b98b7fdc00,-0xad2d76a5c06f61afbef3e0e5f3cd96e1654fbcf66f8ba13e30eaa19431569f18400,0x36c55a7382fee61710e2dcfb86160c76fb68cdfaf72f1c3a845bf1e35e1cafa89800,-0xded3719bc4eb25f7c4b6023b9ae7546312edb3594814335b3a11d0dbb675502ae800,0x2ecc4ca39be0240ee7ba77e897da1db25e7b12b3b6e1692474b61948f811b35d83300,-0x846e9a232f5cd0bd0f2a5d38bf9126d0f7c8ad3f8de5edc1c3ddd1f40380f571a9500,0x14030eb773a5186c7fd90bbfe01ce03caa4c93aca051ac16b13378aff09c93380ee600,-0x29cbf0e63e543dde17e7a7eaca5ee5742ef5334a15c38753564aaae5d0b25e46467a00,0x4c0ec2d42fbd13f700ad326740cf658bc7afe4c704b3de1938adaf9759a4a2eb66d900,-0x79652138607b84bbda71ea75f4872980791e42a3c294f6f05093c373820461faae6f00,0xaad7840ee0b3c0479977de59cf5e2f423b96f3b4bf62ec3afdd0efb517f54060aad400,-0xd4dc8b737b8c334990c77d5ae0ef2bbc719b6a4967ae1196787200510fb6c012e1ac00,0xeb8a5f7d66f0399f8e8944107a3ae4259052822492ade4b72da216ba61e73c67524ac0,-0xe801a542cfc439e505eefc2e0b174b66072feb70a8e092d3a1fbbbcd91508f7e349740,0xcbbeecc62aa8bc27882d8e1e54d2ddd82752de1a0ec3d8bf1645e8968a932070a65b80,-0x9facfef91e2fa8f6ba7f842504303ed39d8525fbe610b0e740ac1eaf855b82cd7b9c80,0x6fb62a0dce832be2edb7621e13b917081234da4172022d09d01d6f295915c4011bc140,-0x45c0df59d82e4e4cea0ef3ceb410db4f4df34772b42c500a4957000d377f6b1cb418c0,0x26d773db0ede1728517b1eb1e2a49d424ca52757a3924897b5d0bddbb90aa132c24500,-0x1343207a7dfbe518f60342c915a7648bffbae144e93d4b5dabd5bd31f6ee8c839b9b00,0x87dab69b7e443b3ec2620517214902edfdaddc7ca6e81c48cc2b359d20da24c9ff6c0,-0x35185f3bfb0a920f614539785d42f906a3abc18d013e54200112b0d72b9dd3f596340,0x1256d8c048e0c40da22745333ed0f34caf2e2c4c6c97f7b0e6cea60b3d9540c5d0a80,-0x5938981383f28e69bde27cc5c7720df07b9cb3858a1be84a95b1bc6bc893159c4d80,0x17c4efdc8bcef409f65513d32b45517a6c508d9f5d527de945d18843351193545b40,-0x5844e09db431ede336af2ddae6620a9757defa908ba041616d5a980e98b6e1d56c0,0x11ba949507c7e37e830e5e24a6a64fdb91ef23fb0a0d76b0cca98c5cc13eb23b200,-0x30e9015d51c28367ce0bb26373cea1b3c462635ad96f1e77592b69204a92044e00,0x72bde2c6125f1c5af5fe4cfbd5326e0e9707a319fabb3d28b3c1bb55ba1906a40,-0xe2531a85a5e26e06669d4b7e5160d82aeaff7df33767a8a9b1cc7881ee79bbc0,0x1724ad086582f25e219fb371c8735a13561b0e77443442674a40d148d60f4080,-0x1ee61eee69ccbc76d25cc6ef3f31d47ab08d1c746bcacc8e957ef5f0a646780,0x21006a63a80776f746eabb018b6c5c732e0fb67700ccdab88b945b007871c0,-0x1b8421ce82df029441df456b4e974615076655b0fa28ee57f4856a31f7c40,0x115f8395ded0a490ce3e18bef44a500464265d677a101f6888f32fbb8d00,-0x7fe0166bc1fb8c62ccadc28652d9e1556a015c10b0961a3671c6d29300,0x28c822e94fa9dd5ec2481466d13716334fd934222fe3b827ec4ace140,-0x87114e19b631b59c236560dcbad71be09407430e444a17efc4834c0,0x109548a7113bac362e9e419f8972a3f65f8702fc007068da36d380,-0x10fb11066fdf498dd057527d820675bb6456b31cc64d467fd480,0x76dd56112a4e570ed7838869d3012a02c0e5eb92904a0fcc0,-0xfb7838bd0888fbf5e609484635f62c7ab8954cd2d06140,0x49d8e0bb2c47369a78a0656c3000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 24 80 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 80 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 55 indices rho q23 m23 23 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 55 indices rho q23 m23 23 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r24 : List ℤ := raw_ints% [0x2f3c439def67b53afb633f8d1232309889b6010f8e54000000,0x42d1315b3493576542833207483d449d734a0a8c00fd400000,0x2cdf4e4ede96e003ff9b5624ed356fc5b4191bd866c1f00000,0x130a10b0ff7b0316517176ddff9223a80c57a514b8489f0000,0x5badadfc040b5650ccd9289e803e077968ce7ce38d1618000,0x14d365f5de6291c0433cd55130d0698111ba7c909eb8c0000,0x3b5c169c56d445ffd9b40178a11ec06a20940ab0c62b7800,0x8813dda3b1e7b0015a147678bab6c7288078fd44992dd00,0xff46e2551cc65fa40c40b23623fc3974fa68493365b800,0x18ca0db6d31e923be712c17e8932de95c74378c4adf000,0x2029181809b7c28f232ae3c53e7582d3bf7296256cf00,0x2304a8f4645684c3c0aa7126117d506045804bd2e020,0x201573d322f330f3d79828753a097040b51ffe30300,0x18bd3807f77dbeccc49d3fc289e6d6d4920816ca60,0x10050593f09a9f122cce7192c81f0e74768a18798,0x8ab9d42604e71e2a626ec0e57e86a1c1fa3c8c9,0x3e45c9b277ceff382f42c961d1f28776f96880,0x16eab0591a432c0c49c5bda7945ebae7994ec,0x6cc4d2c4e0f18640922cffe75c1151e2470,0x195ef172ecd9db1428ecec46e1833481a6,0x47b1d694196143185c320d27c1bcb240,0x90390bf059d93f5dacd2115783822c,0xb80f75c158bd464485d56760d738,0x700b849bed4d4e3d4b2f8846f9]
def m24 : List ℤ := raw_ints% [0x0,0x396b0ddd341583a1bc150339eda938ba0cb1f8b62a7a376d0c6a6be066ccbc000,-0x6703a1373226f05f87fabe8ea82b7a5b56417c6e36c75a642b5e0702322b1b5000,0x597e3eae754a02580ae6a8a323676b24a084652a015b56a13ddbe1796b2be1d3000,-0x322605d45527895b551e7a89c31c2d014fe4d17be45e4f3f9f11b025dfd4bfd3c400,0x145f1bd8cba4a629c8564a2bfcdf2d992eb6164315a157cf2ec5ee25147f2bd6a5c00,-0x6646e68cfd456c4e1f476fec98becc3175cb10ca417bb8f698b1aa3180e7ffc6eb000,0x19cb62600ebf5fa46ae4f0464568696e2a6e34b5358de952e07f7e8daba08e140d9000,-0x55f274bff103f4200346a5d685083198ed66814562d0118d82f2d642ac1e1270cdc500,0xf11750cf387bed53cf2c22528522458940ea39061de4dd31c9567be5224ed19ceb3300,-0x2419c628ee9453f5bf52a5d0e84550b950b0a6cbdaba01566c7a12a2c8d7e67645c6400,0x4ab016312cf97c59a5f5c19982c0dfa01d8ef35e56c9cb98f03c980477a11222b1fac00,-0x86937f0cc6306857eb8cb2225e5a20cadb9e1dec6671e496d7af5cf4112cc2f1556a500,0xd499f91e8cd42cd6d127d0dd6b3e585615e68386afa5345552143fe9fa826970c454300,-0x128036a63a52f072a05b5f99f28bdf0cc1ce60cd260b00e3b0b12b33ac1e460a01207000,0x16cb9582edd4bc7b3ea30da4f2d8c9786a4eb674fa1d5a9296f10b794dac5688da4f7000,-0x18ee72a01e232e70e3b9a704a2aca0af37f5e71378ee8d882aa4e6782fd0b6ef6741b940,0x184278a4301ee6fc2599991dbf441a2680e6ea06f197e35989c0f178730ecfebae3d84c0,-0x1508c53022dcc2f602bc9fa54e32439de9ed2b635400e883a669492b942808644b19d100,0x1043eddeafacbdd93fbf2587affac1b2a1fc3569518514127a10809152515a72303ee300,-0xb387df19a8b66d6b01e81a46a26ee4b4c27a08a7b3fb2cb256384b8d0decc8bab643440,0x6e74b92fe2c754736006b1e1996bf87825b736baca01acdfd36fb5bc615ac1f0c30cdc0,-0x3c8e95f1ab5cbec4b56d585b7f8ec123a23e58b16c7d17601a1e59a5e6b3963a7a63400,0x1d8adfc3e4869e4db2edb6cb959f3a57ba17b67c4df173630da2d99a88fe1fa45bd4400,-0xccc763b346f47ba3d973b8b37a92289707ce7b23015891746bab8257ffd0816c1f5440,0x4e93cbe774aae3fd9d5420c9f2be90e247db7d9889cdabfc1e479f848d8124ab1ec9c0,-0x1a9e2270c75450b0413902ec9bdae5a870f4f8c909e53edeed914ee34f7dde421bfd00,0x7ed842c532bfc90fde0b9fee55b39736dd4c51f2eb00b9abcfd485016f7aad74adf00,-0x210e56cb9fbb060aa6c4991f8b56addaeba7dd2503aa956dcac18df6a45269ef14340,0x77e69d22145b7d4609ead53c780ae7a4d2cb5231a8c1d4f397a7d5d1d20717ac0ec0,-0x177b9c10957416a67309cb42780e52a0cea40c9f86f2332da0411851ed7e11340000,0x3f0e20136b27ea7fb899998cc7fb3d65d632cb262c0b62f4e9b02be8c765330b000,-0x8fad9406e7c01a2bfccbbdd3db913d8b1c1b646f369d6cdd0bfc2daf5d6871a3c0,0x1129eae4d76db122573709ea084b000a34de22ffdb48a210be53945ffd271f6640,-0x1b23cea00e8e553c69f72a18367966cd702b79719ad7c936d7eefaeec29c3db00,0x22ea2289c7d5a444cb2d2957f1ad8f3f952b4a8da067ec7e9b5abcc7ff7d1100,-0x23cf314e8fded155d4eab798d7c6af74127dfdbfc838b9e619aed416b24c0c0,0x1c8f3a06e9fa75e7c8f152f8bf1d7a7a5b33f5b867e0989d59159e49f1b540,-0x112bcb3e4c64006113180c656239610b3f3ff744340c7dfaaff5bc43cec00,0x77bcb7d51b3228e11f76a22ce63902d590f91d33ab346e0186c711f4c00,-0x23f694088ec17c80b1d143b513e2db1f13fcecbee20dd1e993afc1d9c0,0x6f697fce45f0ebf20750ed80e76904a2254d0621987033139cfb0840,-0xcb1eba499d1b8fd14ec672abe2e7add4258c4a22852e4ff3e06300,0xbf4cebf70f383043da5d432ab4adf9c4bf0f8a1b622de25a1100,-0x4c2ef864bb89b060429510e068614bbc767552ddd764010ec0,0x90f13a6aa70da7caf855c9803ce291bb0709bffd64c1f40,-0x25b5397c3acbf1ce2e3307c688000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 24 82 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 82 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 55 indices rho q24 m24 24 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 55 indices rho q24 m24 24 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r25 : List ℤ := raw_ints% [-0x9034cd85e29a6f18ceec5884ba84299c427df1085c8aa400000,-0xcbe5412083c56fe24bc6b5953b34aa7d3d026644a156df40000,-0x88dcf378d433f5384cd7e6c8f3c04f6cab30717e8d09aec0000,-0x3a0a6587a9849aa2b40ae9416274f6adf32979a9fef099bb000,-0x1175217d334ff44ee6e6dc60d4c27ca89a17a8a6a9f61e11400,-0x3f698e628fb122bcc47ae95a216af36f954f19f315a96f1d00,-0xb4a05158b9a751442fdbca0080506759277d50af5a03c79c0,-0x19dc7d7aa9290e4555592a9633044c5df67b34f5258bdbcc0,-0x307a65375e68cad08567e6184c8067ae41941221b92866f0,-0x4b427ae537be024b594d8b070e3cbc8b0176b24fb87eeb0,-0x618d66000f98f218366e3d74bce0b0ef4361a5ccd8e6d4,-0x6a1e738a597f9880dfefac4eaa5abd1c5d13895fc2a84,-0x6120373bf23dff37f883896237a6042b108933ffe989,-0x4aceb96ad3200dd871280486efdf3446fb4b57204e8,-0x3061be150cf9b6ac014a67b04e191146b88dfabc9e,-0x1a26acd35e88d3b9e7fee5963937e9b5fbdf06cd4,-0xbb8cee515493250ee69c3768414253263a4633e,-0x44e909a88d78c47dbbc4e2ca92217dfdc63860,-0x1467f1a6eb66e3b5ba1645c5d11b3baa87b5c,-0x4c02d128131cfe589498ffbc7c75b300b2c,-0xd657b5abc4dd727e8151f00cecee5ade1,-0x1ae2ab2f44072787974195e7ee129fc8,-0x2238ec13d3475cfb6549f41c34d1da,-0x14c598abb5140cc3879d7dc0e7fc]
def m25 : List ℤ := raw_ints% [0x0,-0x6f3f6adc94e9af095c68b6403c77dde87898d1e0f24ccb63480e3102c72cac4000,0xc64111c2e669ec25be6d0354e1304f35ca5b9a28d6fc25e8c22ac23a4f3384eb000,-0xab0a6d082e3032107e530017ed410b6b9498d4718e3a04b8dd3186fcdaa5ac9c5000,0x5f28960d6cb253860bc2f7e61bada6c1122b5d2106ba5f475c012aba5086c13a05c00,-0x265e8208127df5e4c01b829c6e855e026ddbd66642ac48169c2af4a76038c297090400,0xbf281f0fca419d9192598d19ef2b2e26745b9504af0afc81194f0a7618228b3e25f800,-0x2fd38f6e970a7f32baa225d6478cc687741d985ec0eca90c1dffbe3bbb47e94a4d28800,0x9e0a9c8ac383667911eea0f4cb4a9e90cb75efc681246ffe07da164bbe06fb3affb3300,-0x1b785bad00c8505d3a35f8aa1e138784700e3e0a38705846422471ec3cce9e6a2ef19500,0x413a237a6832700bd840858406222b5b1844ec3be63a61e774e32d489f0c8ca6a202be00,-0x85b237bd4ed99119d58522ec1eb184472da585b82d9b1818b40acbabc796f0eea9eee200,0xee9377c7dd32bad42d57584c51009addb24abe5aeaa5d743d4e815e6e355f4b0ec7ae900,-0x1751c26e66bc1bcc52e2264bbe9119177adf1fb956ff553e55aa595a6ac92612617f25f00,0x2020c5ca006becfb6a01fa72d640a072a5661d8e82d02e93ef40fc930c3bc5d276f8ba400,-0x2726f49a18179c5e4e1bfa55aca1fa2075bf65bf52dd961a195e8e2e25cb19b307e2fdc00,0x2a54c4dad263d1f4c7ac08660bc6f869e340a807ec59fe5ddf485e03d914f5eef78acbac0,-0x28b27aa995daf6cd96594aa4412ed20767395ab8b9f965fd46a667ff5a8cfe854bf752740,0x22d7f40c53884bfccbd01ee13e5db07e5f9fb6494f41e270b7d9d345f022882eb4ab38980,-0x1a96cd5b92881604874f8c2fd1725b0f6b2a3f066f165ad338014d350b9fe795408363e80,0x1216bc4588412646da822592e7909d2fbb570fbcfd08f1710480752be27e312d9638a9540,-0xaf79809134b4ab20d0658dbef79d0339ccb5f9dd4acb849880b3045961c32b9314db44c0,0x5eba6738ac3376c943bacfb1f00d2d6180346517e489be64343164eab136d6689e737900,-0x2d77063a7505e5c733dba20aee9cb2a5a2b935a635e0aeb42543e11cdd0391d9471ea700,0x135c1bedac7de69e40cb061e4e6cf5f2cf1ca316dec6ea236174f54f39e9d4ec8449eec0,-0x74b4a36265abde51110ecc6db65727158f238f7b98afa262415b3466f62f0dc73c54b40,0x26c5f999234ca9127e80d83a9794d77bf79b97a543a940faaaf69b55d7a334974c5c480,-0xb4fe52d6e0d3dbfc22e29119864024a4ef58925c9fa0ecb1f9278694a562f0a271a380,0x2e23b13d9695a7ece03ecfcf14cfb08f96477647ab9f81396bfd76fc95c3a1d0021740,-0xa3760d397b2995aa36eb10e201f3ec303dec53a7e7f1154522f30dea873606ef53ac0,0x1f375412f596b620f879e4ea64c10b1c97d1c62bfbc6ce8f122783ffc5f6dad707a00,-0x519393f041c8393e41d25a26a1965b337aabcd7d2bcb67eac6e26d9f8dedf64f8600,0xb485d7ac8d3a961cab95442bdf0de1898c61991311975b03468b8acda07d40eea40,-0x14e4d2faef27578064ebe2229735263490fdf0b936c07e2ad8462772e72384efbc0,0x1fec764335726621eb8997f0bc0c67b3bc48cc1efcfbddeb91664248fafde6a280,-0x279022e9aa48a01d035a9b10124541ab383abf2822d81b581dec49a6e8b98f580,0x26f443e9090323fbfb49460341675adf8240a80ca1e887acaf25972f9b1cfdc0,-0x1db5279d8bea3139a7a01f0510c0a8c451902c236404f390de3a8ce1c423040,0x1100a72e0e66aa6933a05334a7ecf15a495d71a55502c9afd1d06daea1a100,-0x70474bed3f2c84cbcd8c90b0002506d1d382063588e0697292b369043f00,0x1fbf25304149870b484e8be8c19cfb8485b22bf35fb8af7dc65b83cf940,-0x5bf5213051b16831bd2198d5abf568cc06ac9fd0174b3a9a9b0ff7cc0,0x9b89a1e3fab9679570a724b01e0706a48d029508cdfc2a3f0cf7180,-0x86b1979dce1dae915daf5a2e4d7e63a58b7fce8de657ea9072680,0x30d16d51e027384d82f095dd1e3dfc095756ab93c4b474550c0,-0x5385034b8fa9d0de9954a8c992b6dc4202e9d245b9832d40,0x13400ed031c5d40f6f19865f0c0000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 24 84 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 84 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 55 indices rho q25 m25 25 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 55 indices rho q25 m25 25 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r26 : List ℤ := raw_ints% [0x1abbf40929aa497b9f419457eff06185eb8d0df17ace4cf000000,0x25c8adb46ea44adec55b0339a95ad931010bf4c645ad94b700000,0x1959bfb8b824072ab9684fdc2129059c85c02537e10fd4fdc0000,0xabed093817ac712e95147af3106f02ee9a2f3082bb805eff4000,0x33af5bc5f1b249d0246ccf869a70e300a05c00927d7ce6fd8000,0xbba221b51cb5e3f2716cd3b7c6b7a00e138e0362f525a77d800,0x2162359b3f26a26a074d27cd4c7cf6bed59bb17f2ab428f0400,0x4c6cf8eec5f518e7f8cf0edec55aede77381f44286acc05b40,0x8f299bb92eb13b7610ca3439291cb732d9554fb0e84dd0580,0xde15797095add0285fb4afb180781033de050a8241beb850,0x11fa1d07d415b28a3e808acd7dd2a14db7d09c8dc30ab780,0x1389d56c8e184362060dd033109fc9a3e62aa4669eb6e9c,0x11dd956b7ee1311a55097dcc0fa3342415e156fa50ecb8,0xdbefdf9cf8fceda0887b05791dd95aa6f3524ec971d7,0x8e15c77e22933826438a60f526e48325f108bdc8960,0x4cb4a369cbb5b9717feee1024fc13894bea02dc832,0x22563b3bbdb11898e6b05cf7a4d3b9000f3ff7f30,0xc9910562d937a4e808ba3f686e531aa898c9d42,0x3b982fe5a892c090ba5bb3d9fed00f216c1580,0xdd99c39ecacc448a5e2df547b3882153c6b4,0x26fb2ea9bce6e87a23e4ce18b37a045e2d8,0x4e113fb890783b09387139381aa36a0ff,0x6323f0442ee7504585c36fd29e3f160,0x3c04f0613c14a5a0ea1f5c87346d6]
def m26 : List ℤ := raw_ints% [0x0,0xd78adf0b6084c322230ae11c75283df269a816a3d574ca105b9b7ef561e68dbc000,-0x17d9ce40c8a425f14da02b4715b9a3b7d442355b350a11a277eb76f0853b3d1875000,0x147025f16045d22e3d345b5d937562c2e9351d2d9c9aa2dbf2938519c9250ad4233000,-0xb4a92243bb018e57f3b0dc22721940b413e1242709d22deb43d7b558aed36ef4ec4400,0x485145baf3782f5ab18ab3a8b7e2b77d4ec72ce32228983410321addb844186af25dc00,-0x165959aa46d814472ef19098fe2638395e482c442e3730ea549d473561cedbcf8a359000,0x58c4dca29e23573bed167cd4456a0744cfbe2182537799c9f673232996e7435a4f8bb000,-0x122f693e5697a27cb2f01bc185a9e9e8a061fb516ca71f8144bc480af8909ad3507f18500,0x3226269650763ee7532267bde9f612a551dbbaa1b89ac024fd0b95176450512f8273f7300,-0x7609566ef1c37acc38212aca1102188a29d2c6a373c6fc8d82c7ec345d367678af1819c00,0xefbcdd5a1412ab29f08faea825c18af452500bc66e6e562c7d30ae7a6a5d5759fc85fb400,-0x1a7bf150226ec14d83e4dc6b2f3c0cd7b24da5819188dd9f45e9c608f2c39afa5604200500,0x29024bc85322d1407045be028a112b1af4c9aa1f40393c96570e3559fd61f6f1a102c96300,-0x37ea8a0494af3f0466d7348e8e0b0cb0cda3a4d9ce89d6ae1b100297434055dccd93369000,0x4367d529946310b111f46a503458ed5522b2ff404b2592158200d1719fc6c86a5ccd84d000,-0x480e32812097a7a3efe5e5d55cf332f28cadac2fe2d50e6100b4af061a8c2de3e12d82b940,0x44745bd8a479a5642f0807aa7acb6bd74bbd6cd6560b015b29bcc6ec7482fab8508a5d04c0,-0x39e191329a5674f104b1ddd97910121634524b38bce157a79288ff0eeb77d1fe361cd21700,0x2b97e215368dc14cbd0e85f6da28dc7caa61a523f08b29c74fc8ef7b9c750983ee0433ad00,-0x1d401b9a276e053de9527b3bdb01e98ba9d298f5bd8da7d65edc6b478a5097034b77c7cc40,0x117a75be322ea2ff5c644c1e8d9ae369e5037f14c099d2e02b1460a823cada61b2afc115c0,-0x94ab44e41ff45e7dff64c922ea576ba6ddef515b317d19bf32e1b4b3139c8d2f5066aec00,0x4634b11401eba2aec667f937b83e1c47dcad48e3c3710559dfab141e9265fc32db63b6c00,-0x1d62c42801cac8f0c3bc9e1176eee2d4d59286b17485b0ff572ef96357ecce460062ca840,0xadf22d7288eac4ce78510af527ed97804954b101d5e89a72f5f3e3d618cc66edad09f5c0,-0x38ae87cf661e1a76b5a5187ed79e2afd7e9f04b75ccb4a132b16f40a3a736b87c1c99b00,0x1032f99528798e002b3f0654f4b66df206f31aaab6e0acf879299d32077ccfc18799f100,-0x40a1fdca2e762e5b5b81fd17ccb421e4a04bb7c12f2487b0975d1e4b977ceef1ce35740,0xdfa49d33d53227239a0374cc85f8e0cd5de3b02a2c7e367a6bbf3ffd710bf82ef0dac0,-0x29a4622cc43d4a7df3c3f4b97376b69f16d6142d0e04f284a72eefa1b273b7cc690000,0x69e6887ed60bc96637702e7b15df3a5d61f9b84bb3852ac11c4c3aa1bc75d58067000,-0xe3915f2d03f8edcbf9876b1a684b7e0f951c87ef43a3900191f0512d06f10e2b6bc0,0x1983cee65040a11dcabdf1e6bd41a8d181179e68dbc6c54bfdf9e17203807f821e40,-0x25a9698508af7295f2ee41ba35724939d1b2ec5643b91f63a72081d6a10113b9d00,0x2cf3be1608b4a64d350192f708512957bc194ba941c609ec7a9707c96a730dbf00,-0x2a7a6a19d81b1ba8d27a8048bb80fefb1a6543b3773f96361a40aef77eb72c0c0,0x1ef78d6283b677eacfddc397c34cb2915c9c2accf2bb57656718e0d2c6155540,-0x10dd72555b01cadfc5cd64db788c555ffee41fdc4da3907bfc99d54c8203400,0x696d51b420fc84cdcf6b1e72a8a88571089f290494ff977b0363fe8dfe400,-0x1c0d2130069ddf0b42acebf00f95419d0a77431ac64334455e17ffb33dc0,0x4bf183a40dc516af1d4b713ee6dcdbf7256f813371e7235d7defe42440,-0x772101e6aeba65bebe40fc6750093c1359716ba575f78a3e9c578500,0x5ed556546947fbcaec76f7d51080316835da3666efe07c48d77f00,-0x1f46a22fb15b8454f93565438dfa61146f756580932135be42c0,0x301d0d2d3b19458ac25367e7ddcc0e5574b66414679f90b40,-0x9d347328418af8fd31410673200000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 24 86 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 86 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 55 indices rho q26 m26 26 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 55 indices rho q26 m26 26 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r27 : List ℤ := raw_ints% [-0x4d3f46198cbcb8131e937902f472a96a17854d721e66b73d800000,-0x6d21ab601e43a5b4f9f67ab301e1398ce2fad06f24280280b80000,-0x49306bd9b174d69fa3938bf0429c72e12c5b2fa418b5da21980000,-0x1f02326ae086f78c4633f4edf442011184921e334ac1bab3da2000,-0x9513d9238828df009f2de9e3d639b436d450e35a869c97f653800,-0x21cea4b2579f50ad2e821a44a45e02124b5f2ef6b4b62b6b72e00,-0x602f5b9afdb470be5fd3b6cd825620a5793962844aebe8ebc280,-0xdc10692c9eb0f9d19fd8323c5174ff153e889e20331cf7ff880,-0x19bf5e56bc47b40eaa2585ef4a29d76332e80e6091522aaec60,-0x27e9d032c2c16f30669589b6358976fbb81f28e03d34ba52a0,-0x33a797577294729d71ccae7c9e8a22c271593bd17dd0b74a8,-0x381868bb6bf73cc02f6414152f9cf6277aa5181489f9b598,-0x333f537803f16706e41d03e766d508326eb1248c598585a,-0x27649f3a261754d279f7216812cfac0c34b80e3262cab8,-0x196c382625dbbd7d7890ae056435be17fe5a6c0f92e1d,-0xdb5959a624290e4b83fae622a862f096529d7564d28,-0x621241173a89100d2e867cf0aa86900eaa3cc0a2f8,-0x23ef205883b52ad39fd84407fb119b79faacaa610,-0xa9bded941da89be29020f18c46b94344ae72c6e,-0x2763049fc2b2fd00a9d5a05a43f3bf467c1428,-0x6ea9eb4bbbf301c8c1d06fd56be2df383976,-0xdd34aa5734caad4ea2ce36ca3506d63158,-0x118545f4eb2d4ef75c2d152ea1d5bf525,-0xa95172d92ee6e84a63de5548d98dd8]
def m27 : List ℤ := raw_ints% [0x0,-0x1a19d10260b013a1223e5142722fdf805acb5abdd6d92477fb17d45fb6daeb29c4000,0x2deadc2e9c6103e9e616249d5d32a830c2aa5f0b3466631ff01bc01b7eb6465f62b000,-0x2716a4cd0109f341c975a110cc2e5c9f9d070badc8d0e9bd3b4c28d65fc1fec8f525000,0x15729f34598379b9239daaf10728e022e1907ed17823940179cf76731ea57d087b3cdc00,-0x88654496869b54bdaae3f575e61674dd24401ce1282da93c9c2a1d52c37f7ad10dc48400,0x29d7b04900eff29f36b8a521d4fb650389f879989ec002799405f36120023bc572b965800,-0xa4ee0a89afdc2647d243d7e831d3ef62b77a9207452e2e62ae6d1714f10a532f4d5af2800,0x21851b2c4636753de28c6eccd4211c5dfd61a03b67aaadd563ca6eb5e297ce1c5604b23300,-0x5bad0c83ab500205f668a0881926235cd5424301ef56aa5a3dc4b509844324d88f26a49500,0xd5edb3362d10b333121056d9ba6d00c75e1dd7be223b0c9d88fb6e53bf6acf73e6bc255600,-0x1ae9dba2bcbac940e29cce8e5ef42f7d006385891aa8b999f3e32cda4fa308be1f5144a8a00,0x2f209837b86871bdc370fc743d897d4575a5ba852257ddcd33808f118594096634d974ef900,-0x48436ddffba18879a55d1a51fa796c1f6b06f2799f1ac1a2d0b626f2e4bb8b2b29f570a4f00,0x61879cf971665f035106b9a03da0d64ab1fa42e4ae6204c528086900177f15f7d90d82ff400,-0x745191c0083f3b210799f4f8798b35f77aab5fc9a7223a6babe3acd6f12934a972540928c00,0x7af4ea5cc6975aa1979353299c4edf716adc05a544fa03a29e8bb18262d74ef1714a9062ac0,-0x737252f697a2d08bb64f9f911dc12a1c54802a151f094b06bdaf3ab672eca08d9965bdab740,0x606ab03268ef12e03f3bf2071fe1af4b69a7efc3eec3d654472cb49d58db7bbfe7d7cd22780,-0x47adee7ecbb4b5efab194700fc3eefb26f5a40a3e393579986d3a3e7861b4fd2d5e2a5df080,0x2f713c96b358c978ee2cda2c446d7bd9ba72cdd72a34df4d4420704dc5068b8660beaa76940,-0x1bf153da7c54e5fe1a2600c3998532c418de5d6cd07826d1b977bc3c15f6310b9d6a6f570c0,0xea14f5737dff92947b50d745e2c6ae35e17f1d0d8aec1badb1774f68fab9243f6ecf648d00,-0x6cc57bec95f6593d2092da7d2a2d95879900e000056550c2d3760ea5d4b079b56f8dfbd300,0x2cc191d7ea9f69f1dfdd791e6bb4df7431f0f3013f69e98d9ffd0e1700364a60bb57fda6c0,-0x104291da78da6fa14b57fa93fe0f5f073bc27d6f7ad690710098e241083af7a9bde36c7340,0x53271384c95683c769b372888f6566309b9b125149f44f1960e60049f6a3e554b06b60e80,-0x17478731c5bbf1d1420cbaa1de257a27dd7f83b17f095e7d90d59e65f3ff1a36eb9b7e980,0x5adbb9928c7cf62108ac2f349037eda6eaff4461f405105a957e26ea0ba8a74e8aa79340,-0x1330de91a7bae50fe7788fad2733c950b4c1f0829e7a70d7c69986971965491a6cc95ec0,0x37bde7bba5c73cfd9788b837c6f06d0399e85005883cc38f80110b2e5da6474d63b0200,-0x89f0630d7fb624b77cad70975c9c3ccda56926ea0aa2dbd515e26ace94aa7d362cfe00,0x11fccf8b4d69fb7ccd18a2f3f0f4ae035ce3553b536e60764f960ba27fefbc0fefea40,-0x1f40ed4f92b94d62e21ddced73219da53f82a9b6a923d4bded962ba90ae6db64fbbc0,0x2c8f0614bb451fbebc6b99772e828932011cd51b96e5515c269c8784126d61309480,-0x333593c7e9271242c59470110249e5ad2a2322342726b00c4767fb1f1170aca7380,0x2e6de44108afe523dd3de69de16b6cabc3f9ceac4c0638414055ab98ac397109c0,-0x20583cfcfafd991c394c23e7947fcdf2598ac2b4667814cf138a9d3cecaae6440,0x10c19a0bfabaf65b412d252e740276acad10bf55c1a8081b0eb290304a099500,-0x631e9719d2f8ca152ea5b97f51f3b54b65f242bfd85993fdad40489d4a0b00,0x18ced81f794b621f8c7e252992f2222d957b3397c07a439c1efe0ce5dd140,-0x3ec01a6a2cf71cc22fb0d35facd76ae4c6be351d7410e153ebf08cf04c0,0x5b42a368e3dc2ca78e05aca6fcc12d80d51c7d2448a558ef0bbb7bf80,-0x42c3d9c65db45f3af15343098635cb404fdaedf0ad7170956664880,0x1408763f4fc4a74b19d2cdef350dd32b005b3bd5dfe672b4864c0,-0x1bb5b13f9e1ddb4b9dccfd361984b07565a08285c904853940,0x50386df282a2685ef1154cc53000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 24 88 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 88 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 55 indices rho q27 m27 27 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 55 indices rho q27 m27 27 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [-0xa95172d92ee6e84a63de5548d98dd8,0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r28 : List ℤ := raw_ints% [0xd9eb470e190b8d17b87936215ab9f588db477e5737ee07796000000,0x133c0a6596f24b655cd26e4cf68feaf36040884ce637251133600000,0xce4ff513a6cdbd55f17103b8c78db416aadc29eacfab4add1680000,0x575f5ebfe824e64a436e968beca9417e37804473e7531946f388000,0x1a3dc9cbdeaa38e60973fd299a845298e835aab1694235488b9c000,0x5f2af3b991a318446a8266227eab739eb71c4fa3686a5f370a0000,0x10e9e95d9392e017594e40ea1f2d87d18dd89ec877518ee5269c00,0x26ace8cbe9f1b2025b8adeeff626544516bb0a869847879bf0f80,0x485b4299a3184cd3bf5f73f6e97dacb8f4d2edd31dd1e1e4be00,0x7017a515f7c55f97fee9b72bc7b5ccd2f4e008f82d91343ec20,0x90f6f58fb3ad556e371c19c41228fd7800e1bd564b993d4340,0x9d4edd46b26e42dd04047d6fd072001b46ea5259a6f0c99b8,0x8f98827c6165d1a08b34095b9ba534a017320b50a1c950c0,0x6e4862467ab06cf518e2789fd86d05cbff34c84e5e6e966,0x471ac3e2a8b27603ec4744f935c9917ed8698408b4e818,0x264dd4745acbb0b48d10c9e54af7d578bb6482b946a03,0x111b5220b14f0149aabf9096dc8f6f8485c3eea26d00,0x642ad7c849eb9d57488e4f4767852e3b920419a208,0x1d889e70a4aa2e6f97c2b3633bb6d4537397754b0,0x6d7d8bc074e9d54fb23900615f848d745627032,0x133265e562bd12bd4ee8e3678f9d4d7379ba00,0x264e895af97a03b002ba4d522062460e4b4a,0x30743327bb2dc628c6db42dd3ea4570e38,0x1d3486a656e931323bc120ff105b59bb]
def m28 : List ℤ := raw_ints% [0x0,0x329204f49b5526083258bd70bd3cc108afe9ffcfd044b6a8767e2b79724827a0ebc000,-0x586a282a5b4d8d1521348e5fb664bc78151104856117c5d98bc466530f15b858cf35000,0x4ac8675c03a9dadeeb8b1ef2c3974752065993eeeac69c1902ca2d36298c820a9fb93000,-0x28c2a2adde59fee82c8b8dfcb861939c9689e9f60c2424815b1e2c07d53781c36c890c400,0x1016c6765284c7c5a026897bc542f5474ab05840ceb2a29eae102fd514d1c950bcde155c00,-0x4e678e56051e3206d4f3d0d9427ae2992a8a6e1fc57bf48bea54ae2f1d04468d32891b7000,0x132be0c7782d9e5a7d75dcf05fe8c8cb6dd77c3656ff05ba324825a99af3f0c027eb052d000,-0x3ddbb731dc5176ed294f9a01113030799cd9a1a951ae4bce294bf92a21f7fa612fbc51f4500,0xa7d09098d06e7e5e661db606b0cc74a202097859bebfe8fd5eeb87528e6632d968def29b300,-0x1844e66e92ecfbb00d0fee7c29b5799581ddb619ce211a1f8dc024fbcd580677506b79789400,0x306c32bb0ff61688506e47a01d9c9482a741db25f6b32f03d42635651f170e5d2e49eef7fc00,-0x5403b4bea30f41c38050a6b41aa7dab530c467be9c784903af67d079877ed434ed6fb01ee500,0x7f976bb486f6e0e8bcb560a65fb64367fbf889b8c3243f5d91dd4d4bfa03362e4c86ea600300,-0xaa7a5f9392cb0da49bf57e3b48c7475e47fda5e4449e70756531a736204ba4218cffbd9db000,0xc92ff1f89ac2ed52e833a76c2ea682186abc018092d548ec1e963410ce1acf06c020527d3000,-0xd2544d876d07f488eb10849196f1c7a1326d0c02006c831f38fe34b62c2dcd7bb9ca39553940,0xc333b7dd811d075f40013bf5e2f8401421762c52310903a57438cca3012eec59dfa771eb04c0,-0xa10bf4ace5067ce3cc041fb790ca39e93a97a8480211161d90d4a8f700dc9a926edbcc548d00,0x7632a384d3716083fdced4ca97e3156d461e303aad322569579941e4ff4f4c82e4931786c700,-0x4d2d8907d05b50166dbf49a81c0ce105c0342090c26eb11d1edb3b379ef60e6e51a045db4440,0x2ccf6b0918486d5a740553612f1c003638541307e987c2ebfe052456207379b8695a504b7dc0,-0x171be504b6b2eeba6dd17621fa29347215f4f39827efd1ba96ada2ce5cb24f55217fbe6d6400,0xa913484ff24139dd2fca6db1082e4f3e8ef849cf45598135d03feb9afeaa2b3b82b8ce8d400,-0x4465152851862724ca471ae5b48f2dd13206df23aa54663cf730cd9dbd69f01e8982706dc40,0x1866f91907f545189653d13d809256148e37b48bd55c9cd05eca85c2fb79688c6b507c041c0,-0x7a683c3c15ef4dd91bf1b036b250722dec7a7a37ed9d2c3a1a80341c7c107387e3871b2900,0x21920f5ce19c283358bbcd82e2faf8b8f2a3f2a68da371cd225b2015931e245e8a78f49300,-0x802b0d60ec89322aa2dbb5f67dd0f94e245ee81eca72ed7b7545acbf19e572438ad3f6b40,0x1a706348b107d0fc54f4a8e661f1ac86e985d19cb97a2b1bb652b9c299bb5c377c68da6c0,-0x4ade124f71c3944bf69d5a04d9eabd1f74d85f4de00f3034de0941069b349c946ae20000,0xb44292bf0cb33a29191da52ed1948fa1c2acc94cdcc04e4553e47c115f6f858b7223000,-0x16d1fbd9119a85337c03826bc5115e2c6bd210670a259311b7cef63678ceea4497873c0,0x2665c19968db935bad7ebe2e8294a4e28967c9e555801025655c009921c86bc9319640,-0x34dd7ff767a50ddf7c982af81cc795b03e18b8e2051e57c8d890cf511268646ab6f00,0x3a7c3713baebb4259e6609991843cb2139db13d1c3cc6a4d1ea4cb300be9afdddd00,-0x32dc9f2f0072947dd8127b998f3b7f09f99e04cc3c4849160e4e270ed1cb22ea0c0,0x21d9396604ba4bbe91c07938af9df6f925b683ea5f4b2de75148c2e95c06d91540,-0x10ac9bb76bd6075b1c78a1a69f3e9f766a910eb00b9620dfcb54a5dc39f49bc00,0x5d4ce6bd064ecd57ab32c0e6d02c9563af4248cf61c5f3ec9afcd9d98573c00,-0x15f524f228596c2de6ca43e999e927ac940b827c6e936778b6e696b56f01c0,0x33df90b10372f5c7d504c8db8e60803c7682c423f495348ed04449eae040,-0x45ec0fdc9a9b60b964c3be83dfde60089bab1d704ec3111fc9cc5eb700,0x2f002d0749a2613603cf1d295da2b73e3868dd0d7cb40d4d558b5d00,-0xcd435b1f51968f06f763fc03541594b45f8b94fb1f739416c36c0,0xff4630fea906561f166a4b8ae74df6a7d5a78beedaf9333740,-0x28ed6c2df65709ef62e23b0f88000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 24 90 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 90 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 55 indices rho q28 m28 28 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 55 indices rho q28 m28 28 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [0x1d3486a656e931323bc120ff105b59bb,-0xa95172d92ee6e84a63de5548d98dd8,0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r29 : List ℤ := raw_ints% [-0x25969460c6c46ca2b8dc8d6ff6efa0dd4fdd6cc072092bff8f2c00000,-0x3510981b0be1f45702a21dc801dadbd9051a2bca572878ba8981c0000,-0x238f7e4672747a37ccbfe865063cd73a92b8b549e470fe6dab6e40000,-0xf0dc13c3feb21d35d5be63c52f773b01680a3691b547ab1bd0321000,-0x484ef8eb2b65d8908b58486afde1bb464d46a52266b982efbc79fc00,-0x1061da7c990899e071629b52c2b945c7b17226b5fdf07b32a4dc2700,-0x2e8fc89724bd82d93f8f17d14affe168188b0920af8c3a87b27b940,-0x6a69bf0768aad379e423aee938de3b8ea8186d013fd24722dcbe40,-0xc6f8bb1c2dbf33084a6838ca215c43d68249284e106dfc3d70750,-0x1340d8d3400002c1d89b5a19041ff060bda2af1a3fc536ca09d10,-0x18e21ea5cdbcfce36f7f4d6c9d30a3527d5baa2940b8903d269c,-0x1afba9a56f84f08b6abc6d261268f65010dd692207a982f5e8c,-0x189cc3b008dea6a10ddc2bd1d5fb6452ec853c129c72d36f13,-0x12e319a25079fd5738e418594f21d7d1565db90c49294d778,-0xc2aaea9f1d55f77bcc558686fe39e709632c424124d3cf4,-0x68c49d6660d4de3c95d54153fc248b4a29c2ae9f6caaec,-0x2ebde8050ae1e7c748579ed517ed15423e6e3ada28542,-0x11163cfbc9e3effd59d815914a837c0afc69a573dba0,-0x508290bc59e2da88f4393ffdd39ab7262b4be3dd50,-0x12a159b1c9b55a141fc4cfe9f1dac4bd4f4bd3ee4,-0x3430336241055200f27106902769bb90e402193,-0x67fa4f924810898f537fcaaaad28e6c9a5698,-0x834bc0f34f4834fd3fc3970d7f4968bcca8,-0x4efd3005bb487c70e61cd750b42a8fba4]
def m29 : List ℤ := raw_ints% [0x0,-0x61fae999ecf4f9afe18bef0a6ea5b600d4d55fa2a38521e66594743b4d6bccc7c8c4000,0xaa45854027ff39a8d8bbedc93ace0788ad21f3f5cdceae335e97f638c730a32c1176b000,-0x8f1e79bdb02f438d0bb343117995f31139faf23e28b250561ca1e30a6f3299b8221585000,0x4d803a486cb127836f11f96509cc228fd013d5a701e72ba7e57dc4cafe1fab8a4e3b355c00,-0x1e6298732d5cf7ea4fd8478541e5a96556c33890e92da02f2eaa1abd20862607d9de5440400,0x9308ffb4dfd103676b8fea1d5a2b2da52cc196e286c068b69e0ac3f6cf65d7971a63491b800,-0x23b0dc26eb71aff09a15e93a481b11572e7404d2597a349e8e7688632fb9f404ca148868c800,0x72492becb5ace5f314686355b889466a86f513dbd7128883f78d18df6c89dffbd2849eed3300,-0x13397b980d5b75402d879d2aa9127238cc32970069a4202cafaa6f07e71e8b7472097d5439500,0x2c1ddbfa6bcf31e537125772326829b787ff3e9f86d5079906d71b4032eca919ca226c7ccae00,-0x5743cc3fa3d5645d671c4ccf32f85edc3a6e3d28d5534e9d812b563c7f2392b30706c6a137200,0x960b26bb8603167ba198c8cf1972815fd061331e1eaa570b79953d59a12abbecc23c65f370900,-0xe1b903dd0685cd7120d282895093f4e0446ebb64f56947c9b825f0e0af0133447439c06223f00,0x12a9e648e7927ba34e9e628369ef94047ce535b51be3d847f45d07a6e436f21cd61e71559fc400,-0x15cc430d02ae9b7f130b50f05db26d84b023228b9ac57eac34b7d8ad1148b7ef1fc8dafea1bc00,0x168a81410299f65e0e9567f920a72d1f25cf5eca44fa2758bd8a72fcc0079c400a5f38124a9ac0,-0x14ae622a4575d9b94af336a92e00853e2395e4148a676ab5794c4c852b60ac227fa72315794740,0x10db90e1b87e008ca719ddb65d60d9156d2c466b280e5669f7350af3ff182ebc47fe858a0db580,-0xc37475d496c399c050be04d0c6a9183f193f9f8b223cd5e5cdb73ad7c71fcc8c9edc75e9b3280,0x7deb75a525aa79f482eadb73cbf2b57df79722d62584f204d1a7315436df3b35a2d80db833d40,-0x481434ebb42ac15d86fc1aaa7b136a4ce6656347a6d9140f6cf58ec66f12b01e356435cd19cc0,0x249ddbb308444704e845de7cfd4d98ee12ca949452d3915130ffdfae2f30da445604e2d938100,-0x107a99e484ac51c7f0f883e48c9c427c734eeaaf84ae5ea0d63a0bb4c55933852a2f936dd1f00,0x68dd4e6d354baef1a05f6ae4a1d318eee968c76f7b8527c385ce87037aee3cc9c57168921ec0,-0x24beab5a134275afce6d3f874d8d3bb2e4ea2528100ff2544cb0f5456ad349b980382d77db40,0xb4ce36983080cc771e2fba8acaba7eabde40d332f2ade2c7db06ef0e8d489d59a1d4e376880,-0x3093912b612abf9f265d5bbcd1773125c35e715c333e333d5dd94c82b26bf792ce724919f80,0xb56a32899b3e1feac06b0ac99fe1a4605389bae777a42b7197bc16482b0665bc45e7b6cf40,-0x248c257a6dbcfe487f9ffc20bb9ca49fc7d7621c6d40df0c0055b96286992b3af2c007c2c0,0x64e3495b4bb5b79b5cf13152a7467cac67441089814ebeecc3a72eef17e5f0fc2e9d34a00,-0xec525112881286c934fa42501cde8a3f250aff609d77ce80601e8d105b581ee1d49cb600,0x1d0a58d755f7abe0c1c6801fbfaefd22bea9ea06f478ebc108035844122fb52953dd6a40,-0x2f4fb3d65173f363dcedc938285c7326382779d0fbd5b11debc0d2728c586e671d1fbc0,0x3ee3aa6ba638f1e60ce531ff551a8a85df0cf04325078e1825196759121255733b9680,-0x42f54f05756f3c39bf8aa1e58004eb44addacdb109dbdbea1e6e20aac072852366180,0x37d66f8714f6194b51e8041c3bec846ce83a7aa8c7f30c5b3c88962095d8a5b995c0,-0x237cb9bfe08e6b14bd7815a82478ed86c061616e3d113574cc480ef0a784bbf1840,0x109e02c58908184282bb88a5275ea462144e9678987aa7afaf5e185b41a9c56900,-0x57ebc235066a60a16c9dec1e9183cb303f27327b0fe5e43e736bcaac4779f700,0x137307ebb59b20bd5af300cb7e98cd3b0ecd3e7d4839acf88164bd637e26940,-0x2ae63e6bcc80f42bb9a92732835a379388512cdcb8ebe703bdc0e5ce3ccc0,0x359471af658f8ba7a36cd0f2f5d82ba39f7456c322c6a42461a0b763d80,-0x21158a5ceb6544cfcb4e83705aff8f45e757c740fe8dfc2e5399aba80,0x836b6ddfd96beb35adfc818b86f7f33704dd692bb532075b7e38c0,-0x92f1b188b72787bff643db021d8fb7359a7060d14fa54228540,0x14e05e3417ba1fbf85ab7fd1cc0000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 24 92 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 92 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 55 indices rho q29 m29 29 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 55 indices rho q29 m29 29 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [-0x4efd3005bb487c70e61cd750b42a8fba4,0x1d3486a656e931323bc120ff105b59bb,-0xa95172d92ee6e84a63de5548d98dd8,0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r30 : List ℤ := raw_ints% [0x65a9745f67f67462b64e91a087999fef926ddf6feedf14ec4799000000,0x8f79309c88a072ca7451c26f2e3eaa36ed81163cb14db2b4a0f0100000,0x601cd6ce83b41d2d6f628f383278d242468943f1c1a78b062a25940000,0x28abfc0d3c8057973b9cc8f99537b1feac8e5afe1fc0b49645b7fec000,0xc3486995cdf129e28092ca25f59964dc67dddc9e4c66f280c9ae14000,0x2c396d3c363d43592fcb7e89977704e03633cc03ce7a136127b373800,0x7da2f608d08c7ee17178646cf1cfb159836452716b91672b20cfd000,0x11efda9b53a7c51d5b3faaa364361e625304c14cc0f2d8ac411269c0,0x2185529c5a8202338ac6be03a9346cb442bb88f407790cc6f767580,0x33de4841903801fa3d53c19e5ea087cc71abe350b8c084fe138770,0x42fe9c45bd7f06dbc2836ef67d063fd73909dfe6e3cab62e4a140,0x4899b47e0f4fd4f914fae0c9a931f9e07a8a89146b9233d59674,0x422ce0bbde87f1d992136de4ada62847d9b75be2a4fcea89bd8,0x32be51c6c788acea8a30c9efce231392e8a5eea1c8986d668d,0x20a950ce014a754935e6cd3156bc3fafac5303d9941c16900,0x119005fa240a95a9ecec1ffb2dd5a680ce49fc28197b61bc,0x7d3fbbdbc86573d93bfbe92cfa00cd5aef6ab783596570,0x2dbd2cc0ffa65814bdde6fbdbdcc3b07b67151940063e,0xd7463deaca41a09354c74d7c3299a563c0da5344380,0x31c15bdd55d44eb3f251eb31c9915f5f7f41838220,0x8b3212f2172964d01179b2fedf77638ed500ff78,0x114eed613f6ee507d54402285a689967765148d,0x15d25fc6f8c2d9d0a29ba827b4a6d9f9a4c00,0xd1b1ad72b184e8124e922920a146603b28]
def m30 : List ℤ := raw_ints% [0x0,0xbdd6249a3b1aa3c4c4ff1f24366110a19c5d694b1cd1f1ae64cfa132e600dcc314fbc000,-0x147f7661ab8cd514cf7ab8d577b97880cd7899fac95eb9b638ae3defeba9c866561d5f5000,0x111fd0bf43c6139c5309dc0a1123c4ef39582ac3be713a9354e366ad533b3fce5b0e95f3000,-0x936e0c5281e1323e203ea927aadad605fa33db200fb6965eac12c08e24ac57399738c214400,0x396be3f9246aa8c7796326ab300e304616cf68c6a5a5b16ec671cd64d60c88433a860bd8dc00,-0x113f6a6099c699b7232c45d30a4adb9aa2f6ac27a1213167aa39929ff5f5a90d51b548a985000,0x4282546f5750c5e9ec19cdabbde226e0ec8c2eebc13a9ebfbd3933eeef3c7a24abe830b2af000,-0xd363145682836c558f457148af276a8a6e049f0b0dab26662d6f6e67de11be9d5b6f365970500,0x2348681aba8083f783de3e89b2b67b08dbac84387995e31a86cb471dfae0dda6d538e30be9f300,-0x504fef9aa6fef3755bd7df748521fd5a4fe6b3c25ddbcf44047b661cdd3c7326aea4144d8f4c00,0x9d84a72cc5c116c2ccc5ef32e680ed4aedbcac9f540cdc3786efebad7f78a7e17884f8f2ea8400,-0x10c710bc2f4046edca321d5c9dd1c2bc2aa70672b3269ddc1200ea0125c534c73bd1b76d97b4500,0x19018e6a45b35eeb0732294a49ab86d316ce44d447432a947c7fa03658768f301fefb0669c12300,-0x20c2a76a067e74ecff7f479722f9b1b565bcce939152353803a7630790fc70ebdf9acd00091d000,0x25df31be712abcf3a7e1fb1c6307861d73fc6b5e5d7de096db7d4528a8591c67aa53570c0bc9000,-0x26be551d3fc90cc9ffd863003c4be3260510c2becaef80e798ee952f5ea12b29623e9bdbe113940,0x23256bb0bae518e61074c2411eb0675a20b94896f151f8834a5d5f4066409d24403ff88dbaf84c0,-0x1c4eeaf794e1642ff3595344574ba37d959851c3d0700b71ba475ad80fe64ee6d8df3ec227ab300,0x1441b66939bcbb5e1f91edcfc3bab7502cb1e9b466bfdae645d7a372b068121677fae54b0a2b100,-0xce0a2df7cbd66c3571349c345140c4ea94443db5a656bb18beb8a9fb04bd11de7d98e9e2809c40,0x744a44a916eb10f2a59ed97f979f9c6460cfff356708a597b59e2e765dd6ce99203e0bf14605c0,-0x3a3329f4bce5e6c3dc2db2f4b14f7fbe8d64ac4e912a47611b620c271c83b43caa974876249c00,0x19c79f2120eedbe782b1af30dbf348ff3e4ee16b52a148d0e460177dda5a74c8b671b0acde7c00,-0xa14de877e01f26588db0a3e130f643a462313878d03c7e52f34db73c38b64d1b7c2bc831bf040,0x37836e620a7e090cf3d8ca6cd11b59dfb1e2e8ad907242bbc630628e0edae9760a01f52fbadc0,-0x10bf5491c747e30e6dc23e5d13bbe398448447c8b476083ceb3dc4fcc0af17dfc3d8100c32700,0x4686a1e480d0b5fe963a72f30e990be11510262f79fbab70ed095011fc29b870ec75b77c4500,-0x101a44572df566a47fe8337f0307f1e063fcff378494dd744c9f6b9cac3082303c77d3557f40,0x32b00e21b0d725b9583965ae9263a212d4428995939ec3424427c563c009ad68c0e81a272c0,-0x886453e4583b6629a69f3dd844dbb1ddecc5ff143d0e675aa5e40fdf99bf785d039e8d0000,0x136ca480cb84732bdb7d5c22a38aff34af853323a00b753d2ea84c7c42af04fe2b8215f000,-0x25111f7073497dc8e9dedd74ee2c0f7cf41c1cf2ade78d70c8ba4350952809f89cc5cbbc0,0x3a758d63555280ec8bd64cb2bbe0c4ab0641321273445a2a1518436e10bf74567219ce40,-0x4b026dce76f7ba6fe09f2469c7563a96e280e86072d2c377cccd029c46d376c93e1d100,0x4cd6ef7c57083d12ed7150dbb3c1f627d7fbc63f2b8bdc844489f0f5be53cc090aeb00,-0x3d6d559b28d1b1316490b5296987fd2e3e8f4473f7df029dbf892599e7b4b7c6a60c0,0x25452c8ae7f459a683c17a76ef9bace9b8ea3115bcfb7e36bfa8430828f70be2f540,-0x109566eec2c60dcb8c8cfec3c141b6fdfa32599169431041be2d791abeae2d08400,0x52f026d4027def10c1446841995dc0462eaa0f52250275385cda54b3ac55e5400,-0x113d5227f1c7867ff8068d666289eca053f6fc52b14eeb33ca09faeef86b25c0,0x237db3b9da27438b2d6729598e059c9d0bb4f391153c0fc167296c45613c40,-0x290fa37dc52ec60378ff187c8d8dd4c9588ad9b73d5a5569e1db8a1d7900,0x174927a859159900e5e03ac07ecdcd966ab1a2726837457e93c37a2b00,-0x541f7bfde1da1a733bdff92a1bf7cf9b54d6ecdd384b78ecdbeeac0,0x54909cdcb0bbaea09a7c33fe319032377335ad3c75fa3366a340,-0xaa589e9fb2a35379c7a3d07b200000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 24 94 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 94 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 55 indices rho q30 m30 30 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 55 indices rho q30 m30 30 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_30
def q31 : List ℤ := raw_ints% [0xd1b1ad72b184e8124e922920a146603b28,-0x4efd3005bb487c70e61cd750b42a8fba4,0x1d3486a656e931323bc120ff105b59bb,-0xa95172d92ee6e84a63de5548d98dd8,0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r31 : List ℤ := raw_ints% [-0x10de267f03d415a94c9f37451a8b73844befc1fa9645f16d4aa6aa000000,-0x17cc3dcad1eb78a708912cfc0ff78138a0748259f5ec69bc3c322a200000,-0xfefd72de32755e0e136327372eed9f1afbc29939b9b364f9390a9d00000,-0x6bdd998b7985f67be13aa668458af4541d286943fc46fa3f0ac6c4b8000,-0x205b6be227f3a5fd2017a542173a93457ca905ed6d4a9beeacd15c16000,-0x7532160229c005b259a27c527a62b8bffd085b49e20d115d65495c8800,-0x14ccbe4304ed23c19a25399cf05ca4622e0444cc6ba8712abdfe30be00,-0x2f7da79a75ca276488cf6cda606a7862e65576b2a4e4e2c95cbf61e00,-0x58b52648618cba1d27d811e87a9a897246d2b601bab91e6d4f37cfc0,-0x89304a9fd0b1855bb75398bd669a3a1ba8b5b904793548b29486200,-0xb11896dbe332db668ea6144b24322debb72a3cd42c0f7f8d31f6b0,-0xbfcc392c9f909983144ffc8b1a76378b1239013bb1102aa2a1460,-0xaeb5982cdb094ef5ca352676a266f24ce39bf4f2148a0beadc34,-0x85dfa17445aa3035c87a69e198cc2d3612eaaebf67269208a68,-0x561a869df7405b011772f2fc542d864c9c6980c03994d744a3,-0x2e43026365a5db5f97526a997b9898a788347f226cb032ae0,-0x149a1560f82b91dc5d1d896dea59e65401ff3208bcb51b1c,-0x7843142aeb2a82c7cbc49254f5e4c928d53b2d45133590,-0x235720aaa71d8ed643d036679ee9c59cdb6f3de4cc702,-0x828b4d5285d07110e9890c70ccd2d46a10a89fe7be0,-0x16cc5dce1355839a1737dcaa460142ec72314b66b8,-0x2d4c771e5686483bcb2453818d7e70df821503c8,-0x3907b8feb0d630f4c3ae18c6770ff48f1191e3,-0x2232d4a620595b374de8b0b45c670851d920]
def m31 : List ℤ := raw_ints% [0x0,-0x16fcee6ead2839d4d3dae4c56295c10391ef4fc0187d6c441e35248529da1abb9f8a7c4000,0x277cea732cf41967e0ce355087f913f5270c7587f05e96b94e3e0b5b0e3d60f9c6d8e8ab000,-0x20cb0e34c30bfdf8b36ca511802d0496f01c5e38ba15ea0622711ce3201cdbfa4e7b992e5000,0x118969c601c896d3fe721953516e529ac09961d96519ae1665a009b247a7d20e52f5aeb69dc00,-0x6c9538ef475bc1c70d6dc2b095bb80936055d4af880055432ac309c9dbc77fcb7c3803da78400,0x2065a661c96a932c5305bdb778b7fccb0df9ba2e0f9cdcd7927b994078589f043e6805d6701800,-0x7c0e5ec19932a524ef420a2a74bf2549e31cf11a5110d099acfe16a62b2fca4e0d9059bbe76800,0x1876c62555f2a57a00e7bda34fe3a9eb10f3a07863b091a3d4fe286105226324eaac9ce689c3300,-0x40d64384a1a6393a9eccf20396afa0f86ff7fbdc97fa20411827604f2de81736bf4a86e4ede9500,0x9269e89633b23152372ddf1c8bb0bb6e02a9920ee80a467cb8a5f02a9d616b4383c3b77f5fec600,-0x11cc7eff42e839108fee52b1178a459eaa0b7841bfaad8e6fd51540ae6883309636020b928d39a00,0x1e11a987e67e584529e771597e71fee3445354aa07abbc8c8237ded73a708bb41c11a52fdd071900,-0x2c6866090b3d9ca576f869852fb665ed660cca015990b1e4a71cad003301162d819284bcc6e62f00,0x399f451a7fe84125ecc79e1ffc2a2f260682364de7571592f88d63650a3b67eeb92e4a4b97031400,-0x41f184e3d26fb3de4d539c2c793c259d7320415a3bb5f85590f35f1dc027b6ac9dfd786834d56c00,0x42bf8366f045b5ffa833126191677899dd3d6de62a307be173974e1f1a186747b4bf5ed078660ac0,-0x3be05fe5d3bee66c3ba833da7e00dcc49c1873704e979f5eb3e223b5f2469a85710f2cc25764d740,0x2fa92e2242fb5eb1c3434172cb939799f0396e7f45918f90bb8ef598dafadd7a512a21209d4db380,-0x21ae964cc3a0b82e105fb310c2c8ff8c71483d5e5388aa044a08bed11ace7c73061f07efdb5a8480,0x15219d0aae743a7193bf20005fc07ed8603d8ecb8b56619d2f652dfd45cf4e971d1b12b01f0f1140,-0xbc2cc95cd205d4bd339898cc9dcd95ea455093f1c91cc85e2353f5d1214dfa17cb427ce859ec8c0,0x5cc9b815fe24bce41cbc8824b69e4642df9ad7bdc487afe0c2632efa6e79b4495402f5cab865500,-0x2874f27b8376c2732e792360106fb5e7530d6c37660e557714d57ce886e61daff1aa416b3e48b00,0xf8eadb1cdd5bd927a77630aeb9a4b29c8c2013fbe3c06d39b97a7fe4cd9edc06929246335e56c0,-0x54246230327e5379179cd207efc3f666291537a5fa7146e3af15bc384629ee389f0c5ef4508340,0x18e6d800bc7edce0fd8783ebfc28bd3998668163016827b7231d5e9e9bfc3eb868d22852e75280,-0x66bb3ce9fd759837042270b100e324084912ca59c3e4e2d08fa34300dfbb5b9849f97932d4580,0x16f199abc44e8e9705c31c684ac30c536b7eec240eb12c496475001d6364dda0df4719221cb40,-0x4686e488c6a132384a171cc785adea3ffc7259cc393205cf5403f119200c42262451aa1e66c0,0xb8f9a5009644579df6453ae7be1240f885c5377941cf4a9d5b7403e58521a4e64efd8d95200,-0x199fa5af2e03f173c5fc093d41c7a04a56529e8b613ae27be2716dd84cd346fdbbb654eae00,0x2f733c7afa853bc06bed5496f0713ad8214652cacdf139f6080e315f070b9e31bc0b016a40,-0x486e9f6200440bdd0a0e9d212c550d3a007c479e7f52aa00a98239fb9311a6c44f62bbbc0,0x59b1158659a45edb9acbc35b63d758d098dd816ad2a83374083ca8c8ef0dd50780da2880,-0x586135730f433840057825f6987d3565193439ed4ab25f143c2de019dc9143463763f80,0x43b5caf49ee98ae6796021b62cdbe2872e8bfd110152d0f6213b969ebeeeb88b9ba1c0,-0x27353b3a61a8c6f1011fa265dcb31e9fc6ba4bb2a802e00c728d7c76fa10067af4c40,0x10926ab52004a7b61e29748c717adf3fb2a800a26f4775bf6d670a724e236a6f1d00,-0x4e505b2cbc2f07db2018acf8eb88ca098d71c95c1954325bc43e300347dda20300,0xf4a5f25f3dbad972a0ba87ea716ca10b2dc62cfe66f96fe4ff92c5b91e9dc140,-0x1d5f221c368d9edf70e8286be11345b34ebb9a9719c2a630803b8f6dc2ad4c0,0x1f78311cc869f685ce781223bda495da5be5cb602326a730554aec36d6b80,-0x10632e9ca40ebae43b2fe5a534f07fd86ac62de099e1ea2dbf03f25fc80,0x35d60b7a1a4fa8d36387f2732c903ff2f22308b411a43975277accc0,-0x30a7893e7c3f05ff832a1b5520967753efc88a470b55531e71140,0x56db5bda5be9941b2d3031023000000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 31
theorem quotient_ok_31 : quotientCheck 24 96 31 num den q31 r31=true := by decide +kernel
theorem quotient_source_31 (size : ℕ) : (coefficientsPoly q31).map (Int.castRingHom ℚ)=polyPart (key size) (X^31) :=
  quotient_from_check (key size) 96 31 num den q31 r31 (num_source size) (den_source size) quotient_ok_31
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_31 : cachedMomentCheck cache 55 indices rho q31 m31 31 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_31 (size : ℕ) : intPolyRF (coefficientsPoly m31)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^31) :=
  moment_from_cached_check cache (key size) 55 indices rho q31 m31 31 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_31 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_31
def q32 : List ℤ := raw_ints% [-0x2232d4a620595b374de8b0b45c670851d920,0xd1b1ad72b184e8124e922920a146603b28,-0x4efd3005bb487c70e61cd750b42a8fba4,0x1d3486a656e931323bc120ff105b59bb,-0xa95172d92ee6e84a63de5548d98dd8,0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r32 : List ℤ := raw_ints% [0x2c03ceb39a4a9c3e2389c00901bcebc8a03d82045a4c6aabce78bc8000000,0x3e148621eaea0233ab947cc149c3f8b6bab11fb0b57e873f74bc61c800000,0x298f935982ae27291e8c1eb45713273a2751c2a45031b0149dfb993600000,0x1193400bb4b97e21d0d6ff0dead3299141d3720d37ab602ab633d18860000,0x54530721bfe89e5ed52c37dbbf2f196ffd0bad178d7f13f4d7296d7f0000,0x1314d5b848c77381c52916360710188ba739749a233e0a456f0b2ab44000,0x3629ac80330e910f1ce6548588704d4a28cd5f8c5df5efb979b49a43000,0x7b9ce714509b3b84e5196e8c30b3e3d5760bfdddcac46fbd784df55a00,0xe6c9bf4378209814987953a89c3a8d9a70bf86c175128cc7f8e45c000,0x164be1aa274f74a748515b5f820accf7c3614aa0ffb291de23d9be640,0x1cc45b47cd1e684edefc9cc0009c1a76b3a328d20b73ac1f98efc080,0x1f232bb976fb131aa0b3a6637b3a4725ec420a8ed69b1dfd98161d0,0x1c588a90d6d27405e6b4a5a2bd0302f4bf3801a1d6248b9a2efac0,0x15b4ca1bdc34b555665622f019262df11421e91ed893b7ec730cc,0xdf3749122bd0b02028697fba9d5ad03b7ebc791a268a2bbc158,0x77d6c2b89d32b0a9a8e323850bac0611b6ad64eb80d10a80dd,0x35532a7ced65475949ce669ce5073cdbed6a7bc2ffef75c00,0x13701f34701aaf8864063a39a2801c1d5b43c6ad671fc0e4,0x5b4e8a7c77a58b885cb78ecec3bc41c28f7d92dc8ba370,0x150ef7adc3dbccb508ab7454753f82b62243dbfa8447e,0x3ac7167b6d5c75d35a36589540b18eee81cecbf7b00,0x74a5ca011d7539c06df77171b2dad866b29bd2a48,0x92aa918f502c74ffb0a00dad1a30e9a884d38f8,0x57d33c1024d29cc56bf4a4341dc66a68f5c9d]
def m32 : List ℤ := raw_ints% [0x0,0x2c8a0df66f7df00c5a781b3e6f0225f6eabfaa842f7301c3fa86f6c2011693cb851c50bc000,-0x4c1531c84a2d02c66f5657cb8975d452ba6f60b534de7ffa80638e49902b37b4814442cb5000,0x3ed192bde38d77286b2cd12c0d4c5bf469e156b60672f176c1c73e0151678481f02b45d953000,-0x216433ef07f9eb12ba76c23e7291d72179ae8c2d091cc72cab957adf52a98254d8868a13fdc400,0xcd749a74358f855138069e519fd864325bf7676c73ee3794a9dff63f560838dd84e5ed87105c00,-0x3ce6634c4cdc0dc2d35f39f6b6746ed8b21a17007d70aaf416827472fec1a4ef90cf0da8be43000,0xe79ca1f51041aefba3da449c201d11595a3206c947ceb336357ce68a72f6edc78e6bcd8731c1000,-0x2d595fe66b914864709a7c1bbabc0bfba8411bdcc8680bbd8783ccce6199498164f7e429d718c500,0x774b9ffff3b9e19037fa40d906b0b50590f3f5c3a0c517dffa49c340cf2b1287003ae9a30c403300,-0x10b4b9ec9332a213a7d75149b56bf234829e6b3d85501ed622587454a41bd596d92dd6c718783c400,0x203aa8c51ef746fd7f44c9099ca838c1b66e809bee3fe75f4691d806c3d45091b04d2dce2ba494c00,-0x35fb7e1277b3e7b1015fb01f83273f90e9be1d8e9e2f25fb75ceb76e024936e6a3b6e7092723d2500,0x4f029d0ffeabd786ccb68aae8338b0f80ae907cef0190ea6271bb0c5dd84bfbc5b362ae9583c4c300,-0x658e4f52658c8ff9abcd87dd8fda33ce353e7cb4a369529ebfa8ed70466026ccc07fd359b68cef000,0x73121db5cebbf4b74ba3728915ef349a92db50cf3244a8f881b1fcc73982541715bcd6fe70646f000,-0x7342993504cfd697dbe15832e984aef4b151f8f3c28fe93430d638adf998bea7941ab137562aeb940,0x6641d5fd9b0a6a8fc99d6236cb9fdece5508cb498cd882e98661a1b2317527023e35151541cd284c0,-0x50733c83cb16c421b4f8ff2e89acf700591b69b121e6d34d1795478a229898b29fcf95b8c342a0900,0x3827f6b263a45466e46c89c861cc68eb49c1f909068956285975a90c61fc877161982e6c2e805eb00,-0x22c5e1ab5baa59e9cc63dfdd56672da1e0ecb1d4bb857f753f584c393a71e2c8ee6c42d99cbb1d440,0x1316272aaacabf4e2e9f8286c9d8462c6a7bdfa4ad3476043456d07701140594754f08430a28eadc0,-0x9460af08a4c47d40594934d7b7841f4598a42954fbf280d54702f48a5f87dcaeb8b3fac9b2479400,0x3fafb9d76a19adbbcae632b7518d8ac434f39544a1bbb46a3acc79642978926867900bb6c7b56400,-0x1815516c383634d5c0bbd4831928c0081a5de8399eb9a867c92a8eef86bfc379519d01f7d6e1e440,0x7ff1c1f7b1285f204e769be34816f68823b5d88734800a1ca6599525828489d599109fb14ee39c0,-0x25257ae5b2791cdcc2fbef4c9ca44460a15316201cb59fdc0c87f8a5bbb679c9a37a88669e01500,0x962114e55d389e011c0635819635a7d99d7a276c7fb1ecc3cefe193a3eb864a879bdad51468700,-0x20cbff41f05a5e9f0c5c87938eaa91a00fc55eeaa890dadda751438da44d117f32978559859340,0x62718681e05129c9f585573fff51d62623e69fd883977b1980701597d54c4e2756611c73f3ec0,-0xfba49ae1c62b5e6e97c22ecc4614830b578838425d7a0372ff65b568145afc1fbff2c4b80000,0x21e70fa792075c177ed8cce8d30f03f6bbf3a35398beeecc459cdc6b064366c538dc9693b000,-0x3cea45257b4d19070723d209db1be86666e97e6bf358bbc4e99bdf189f51f107fb2da0c43c0,0x59fbfc58d8048eb39a7c48461a710b940158d84eefc9991f91fb1c45cd677ca19c95f6c640,-0x6b82abe0af3ac2e6a867aa5115d2e583505eb4f73cb341038442755bc9d9bb89945114300,0x65e034213ec956189aef132ef8c4d453ba26199936dc74e3c0e04c8207d294a09e2e6900,-0x4ac71aeb3975321e5b883ff40e8467757dd364453c6fe4dd9eba428afb11e0a46f000c0,0x294fce2c600d6dd10f35558d091efab86e0abd1cc65c308070291b8cf73d6898a0f540,-0x1094ba16ff12b44697be326ea946263901bdf7b01f1d2395aefd2868161ac16eb8c00,0x4a03c3f330bdbb5bc02c0698d9c49527e833b324d57296db7e650aea3ab4d6e2c00,-0xd91d9da662b4c5650b680b2af9c0642b890ad258f07d2f18393c47841bf45a9c0,0x185076bd3079418d60c318bb4ca37bf213bf87ad7ed6603126e56603c5f13840,-0x181e9b42a26f6fb37755487056f792c0ba73cd48fd5ad48e80637fcb6f4b00,0xb880081749d80131ccf1f7162acf01e19a7693f30885bfcf33f70146900,-0x227224b784988dc8b6983c7187c92394f05b16abfcf92a37d682a5ec0,0x1bfc95d0e47c538a1ec2720aca41542a7c931622bfe0570f3f4f40,-0x2c474f37f3581f0c79646cca88000000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 32
theorem quotient_ok_32 : quotientCheck 24 98 32 num den q32 r32=true := by decide +kernel
theorem quotient_source_32 (size : ℕ) : (coefficientsPoly q32).map (Int.castRingHom ℚ)=polyPart (key size) (X^32) :=
  quotient_from_check (key size) 98 32 num den q32 r32 (num_source size) (den_source size) quotient_ok_32
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_32 : cachedMomentCheck cache 55 indices rho q32 m32 32 5305534239971966886293720722628714496000000 31=true := by decide +kernel
theorem moment_source_32 (size : ℕ) : intPolyRF (coefficientsPoly m32)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^32) :=
  moment_from_cached_check cache (key size) 55 indices rho q32 m32 32 5305534239971966886293720722628714496000000 31 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_32 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<24 at hj;omega) moment_ok_32
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30,m31,m32]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<33) : intPolyRF (mz e)=rfPoly (C (5305534239971966886293720722628714496000000:ℚ))*rfX^31*(1-rfX)^23*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U7C31
