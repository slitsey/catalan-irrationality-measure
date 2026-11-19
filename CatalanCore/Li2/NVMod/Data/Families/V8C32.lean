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
namespace CatalanCore.Li2.NVMod.FamilySource.V8C32
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,8,32,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6,7]
def indices : List ℕ := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def num : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def den : List ℤ := raw_ints% [0x1497b6140ecae2340d4c400000,0x1d89adfbdd7a99a8fd0a940000,0x1423eeb43e35575a6b088c0000,0x8b04cbe62174b5583ae653000,0x2a9b11d3a1656847066a1b400,0x9df9d627029b54226b8bc500,0x1cc46dfa035348c21b21f7c0,0x4390786cd3eb840d1b04ac0,0x8231c7f93b288d3158af70,0xd06813b033b2925c11830,0x11786929902340d019e74,0x13bf0c1712484a4812a4,0x12dec185613766fd431,0xf43992e07a2c0b928,0xa71104354435486e,0x6059f84a6e016cc,0x2e979a4c11caff,0x12bb9ebac7fe0,0x62fbd6a3c88,0x1a62f3077c,0x58934a7f,0xe13c48,0x197b6,0x1d4,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0xb,0x37,-0x8f,0x1b5f,-0x8f,0x8f,-0x3272b,0xa16f,-0x10d0971,0x10d0971,-0x4e0139,0x578e6f,-0x242f7713,0x242f7713,-0x321567b,0x28b1643f,-0x1b0db09,0xa9aded,-0x3cac037,0x19dac177,-0x2ef7dd47]
def rhoDenominators : List ℤ := raw_ints% [0xe767c9fbea0,0x1fcc4dc60,0x1d99e20,0x375ba0,0x626a0,0x9f60,0x1de20,0xe0,0x1c,0x1a94,0x12c,0x8dcc,0x330c,0x6b4,0x444,0x13fec,0x11c60,0x1ba0,0x20460,0x2860,0x2860,0x34fe0,0x8595a0,0xc007160]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-8) 0:ℚ)/(rhoDenominators.getD (m-8) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 8
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 8 32
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x57f5e6c6d698cb06143e92558900,0xbd2ca54415ed60c228048e78a62c0,-0xc5de93e520b6cd6a7b599540e185c0,0x861bbbebcf0655d277f64266daf6cf0,-0x4235310e4688844d158315d44da40430,0x1960168a37f804bee193418baa67841a0,-0x7dbad3b363908e1f3824d9b83d6c3bca0,0x205419adeb3103f505093c5c6acb94112c,-0x709fa86018444e416b2095372d799ce27c,0x1512a8b38d1181f8e3419c7fe4fe0ad8da8,-0x36d4e4451b61d002a988631caed469ed6e8,0x7d1c29819569f5a64685e692d772fb5d5d4,-0xfc19e4b0445d55aa05c3dd433db10355da4,0x1c3297da04e089eb80941b6d8c85752301f0,-0x2d05382ae5c11accf9711857ea39356277f0,0x405bda513e7587547b0a300201d259e30cd3,-0x529c4a085c916fdfc13ce62de5ac18f6dde7,0x5f6add1d978e17e1aae83c390a7991942902,-0x63539a904123405ab40c55c3109f6197ef52,0x5d4818c49dfdc1ec591797d4c01c83b07191,-0x4f13c05a51cc29de9ddd7a0f493578e665f5,0x3c838cc531bc1733db0c9c942970e899d4fc,-0x29c930d5dc9009d10758f9e92a28e42a62fc,0x1a0360c1d30481496cceadae38b894695f0b,-0xe94738083f2e350a2710c3997489acedc0f,0x757e7b6fd7fa8760125c3283080556e0076,-0x350cb7b3b53e327f61852bf804ef258da46,0x156822f6e834e59551b529ee44f7fa83fb1,-0x7b0f632f3ab9de0ff3331d6f0f34a91b45,0x27307a0f5646da037c3bb82f89748a7d98,-0xb0054356e38564573847d68ba4de24818,0x2b4544fc3a503202c3e7a0c52c93b32d1,-0x93da3207c190c35ddcfb9aead09ed60d,0x1b2a57dc2a55f7bd61782eadc90bd42e,-0x43e4f339f169f22bc53114c7aa3531e,0x8e275671abd87bf0f9e6353dbb8c9b,-0xf4c080f5eb986e0537cbe344c9b87,0x1525baacb96091c6814eacc6c111c,-0x16bf47e57f00100ac794f9434b9c,0x123d240c39aa14200577c0ddea5,-0xa4146a26c1d1dafe4496e0001,0x3afba5d1a3ffc87c20648ab2,-0xba3b42f3f32b88f05a7b62,0xf209e5aeb6861486d0df,-0x403646d5e938a065eb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 24 43 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 43 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 54 indices rho q0 m0 0 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 54 indices rho q0 m0 0 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m1 : List ℤ := raw_ints% [0x0,0xaa6c6f213fc8095bc7393b85b9700,-0x16a2cda3b0dd890abcf40dc10fbf640,0x1763de5c6424b8a7feb2c74a8d21ee00,-0xfa857c949c7032c312a4de414ed06510,0x7a203861692aa068ce23a8e115d256740,-0x2e35081dc1aeda75ba8d51a77be4d2a1a0,0xe1f3fd150e95460ce2b097df06a6c7e0c0,-0x3952a1ca3a7c119b6796aa8a2307da13194,0xc4f8ecbf82fee884ee1bd4b7e592c3e9e90,-0x24575e92359ca9a5352eade159c5cd7d2ce8,0x5d3608faf82bdca7bb1f4f542a0801ae6ff0,-0xd1936745dcf01018f8e50f5f2c379f24e03c,0x19ffce89b7d8daec995245aa6e0311d8a7f00,-0x2dd0ba9418467803ca45d6c6723b305ad0330,0x47ffbcb7799c9793b6737aa325d294d563060,-0x6543daf3f9bebec5cbe2bdde1c1c38694f06d,0x7fd3fcdad5e5c0e6e428ce9394402af504c14,-0x9120b1c5bea4c8346e7e24819079e6eda79f2,0x946c0bce476abc22f3d0c4bbc1c40350382ec,-0x88de4f50d729af81826f438b44f269c520103,0x71dcb44b5fd38b9cf0a23ff32b4d59dab7ee0,-0x557440780ba2a3d5354778f0aa39917886f8c,0x39d4e686707164025e2db9e9ae2243699be58,-0x234257ee8155f09fa2f6cc818dbf95d08f9cd,0x1356c6e3a5edc4ae015526773a57a2664baac,-0x9861074dd41f621ee7b2f7d1627b51a87036,0x4335190b10aec16b802a9951f1ed33873194,-0x1a76f8f51204955341fb54350280bc377ceb,0x944b908345b0c16a8c64158dd30bad65b08,-0x2df9dcbfcb090cac27f647f4f761c15e278,0xc8c2ca6e13b5efa322b4c041ee37337c30,-0x2fe7e2155baa40bb316be53792268b3e7f,0x9e9d695798ee651ef57ef1fba42b07cac,-0x1c2ee2775d81c3bf55d9c078855d0ba9e,0x43f6961355a4c73f466e75fa683cd194,-0x88ef9736d37c7df5fb7cf23b214e1b1,0xe22e60bd2a2c210d3b8fbf2a7ebad0,-0x12add22da2d22c0794e5ea5fd8966c,0x131e49be126a5236502a00b5f73d8,-0xe818aee63de10f1ebe583de58b3,0x7aa27ace741c0834d6c9657484,-0x290e5ed9c394eef5bba562ad2,0x77496299faac0b1eeabfc7c,-0x8c5dcbe04f8f947aa2815,0x20ff274ce58f95bb788]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 24 44 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 44 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 54 indices rho q1 m1 1 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 54 indices rho q1 m1 1 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x14a3217506b939221d1fee353174900,0x2b58ecf9fcd214e0db0c6b96e74eefc0,-0x2c42cde6ff1fa730be5b88104d928ac80,0x1d4558d13e42af973c66f1a0b0d6621c70,-0xe17e68edefe357724d6cfd808b79a96460,0x543e8def07d51cf0381a454c180097e58c0,-0x196aa83024cd6abdadf5049b00dd7a696420,0x65d0b5a459eb2f230c3db468c651eefbe18c,-0x1592aae084a9a8fc439e9c128e1f8311d1d38,0x3ecf4eb9ce2aaa9d61d811d177030729c31d0,-0x9ed6bbe1ef2e53b29e7a8678d4938331f0228,0x1600021589a7fa216084161e2b7e039692f00c,-0x2b065993551601c12308509da2048a49ac0370,0x4aac184e4e78187fd59f21242c9e6b7918a340,-0x73874a7f7170b9548e44607fe9d379aeabfe90,0x9fe69ff5b1e8ece2b0d9985895634583c8afc3,-0xc68a48a70231cdc62ef0ab2cf60c0354a75186,0xdd9ca9e20749de6e5af61b8f1591ca304b04b4,-0xdeb586585de9984df9b9c9ec27131f8ae74d12,0xc9b27a91844ecfb5621b8ab9a57265b3fc1ff7,-0xa4b18caa1e34e1fe49fd74fd4c9c35777ff37c,0x793e1ed2bc92caccdac9af13d971ca87e69630,-0x506e020dcd03aa29d474bd6346257b1cc32ec4,0x300833614026b226f75cbbe8de02f75394bd97,-0x19c8bfb9a71a6b5c78103af92e68468c8ebbda,0xc6ab06dcb2ba0a1538aa1e8fd139f45d9c9e4,-0x559a7502f00f77a567096f4babb3bc649337e,0x20e5b256f504f625a00abe8491e183bad929b,-0xb3b249c03934f8c75dcf8527bf1c71d88278,0x363d37ee1b2e3f924b3ae8c752904e67a240,-0xe6421d7bc64bde8d8f3b649069bd510ef88,0x3555145b77c9164b3978bbf24459ae1f3a9,-0xab1839288b372918a3f8bfcfceb4fbf03a,0x1d655ef979bc46f6642dbf8318d74470bc,-0x4462b15ee4f24b0c3f9d9fa56e6fe8f8e,0x8490213ab7ee202c45d73c89de866855,-0xd1fd000513d5deecb67188d418fa9bc,0x109185fd3d94c44fcc7e52b2a347b90,-0x1020c544fbf4e6c5c4a8c4dd9632c4,0xb929d0dcdf05641956962ccd2531,-0x5bdee3ead0795f8dd0d3bdbe5ee,0x1c9e7760b88e47442519962f1c,-0x4c725a3ed4f1421ae7e9ed7a,0x5162e533cf5d8919ce30dd,-0x10f3236fc95cbd9fcec0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 24 45 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 45 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 54 indices rho q2 m2 2 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 54 indices rho q2 m2 2 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x27fc10d2bd06deb2186ddd870fd1d700,-0x5307986c6b5c23c040b0c037f6a7a8c40,0x53cbb7c4403b6023e8831df2cbb2b93080,-0x36c2a07984d4fba42a5d9e1227febb37a10,0x1a0c26d0ebd5bb541ab1ab729899d103bf60,-0x99c7c91eef6c056cf20a3df062afc4e91ce0,0x2dcfa133eed5f13fc15a7f61aac560ebdf9e0,-0xb525fd978657d5499ffd89a1978e285938a94,0x25e067debf5afeb07f9c30b8a8b2e3a67e4838,-0x6cca910a460510159ebabb6e8df9be26940038,0x10f52845ccd3319a4648b9254b4b835939a3e18,-0x250c46ddf2b9bbf53e67381c857cab2f39b55fc,0x47670972a4f0a50cc2df979488601309321a3b0,-0x7a142055dfc25e1aa566e4069cf750ed91c3390,0xb9fc2c474d0cc40b14deae486402e38336679b0,-0xfd5f7c041100a824ccad38a39afdb90d2bcbc6d,0x1358340bdef81babc6e08b8f391725ddc1744e06,-0x153ba552bb3e7a1666dd68c41d22ea01233da3d6,0x14f8cb44283b76042558f5dfdb10e66f97b143be,-0x12a8232775bc14216187f544ef1d084d70b20633,0xef48692dd8a92788cebd667e34733bc519581cc,-0xacd164bf65a13504ce38c5ddf8e201a99d87624,0x70651f30fd75838873e47292a42f66896fc910c,-0x41c16fb92ded67e5cd8331119a6e28b1886899d,0x228d50029215f013951215360bf6aab9aa6614a,-0x1045d4dd0820abff943560deb7a61821c080222,0x6d9caa1f0838ebefa5469ea674fe742453c2c2,-0x291cefe749c8f8fd9b72e62ebf6230901a840b,0xdaede90f2ee7380ed1d90865ffc33fa21b218,-0x4056327a5c570c52e49abb9ca337693565a68,0x10987fbacf97afc6ab8a3ed0e285e8388a658,-0x3bb20d1f86440f700383af774febecf2801f,0xb98ae8074a0a4c5bf1656cfeacbce06f19a,-0x1ed22f19a4c6f0b0b404976e6dc90d21b5a,0x452836beea7187565c9fe7a98f33d01fc2,-0x80f1d1fca8ba58e468643034fab000221,0xc3d366184401257c8bd6dce8fbc94a4c,-0xec18889c5a2814621db6489437d7ac4,0xda75211dc66ae4790666cda608044c,-0x9426975a44e4382b8acdca3f36343,0x44f909b75f91dff5225f6daaac9e,-0x13f9c1b81ce0672c6713793d676,0x310382bc10a0fbd857665dbe6,-0x2f2d99608aa079877bc2f95,0x8b42088bf06802fd9200]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 24 46 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 46 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 54 indices rho q3 m3 3 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 54 indices rho q3 m3 3 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x4d7860984e3d4f790f54dd35aea690900,0x9f13e83930dc18741adebdfb28127073c0,-0x9eb88dde9e6f8f783d606e6c197ddd40f80,0x66853c4f1acaa92fdac9e05517410a24f870,-0x30300aa35f989568df8389adcb78868271a20,0x1190ce4892f501ad891db4919b525f802272c0,-0x52b068801745eb71d7eb97680ee87f13961660,0x142d6541a3714411383f266207712b47c7c178c,-0x42a0f0c799f50f98b77851168a1fec5295f79e8,0xbcd67fd9241063933c594a38d7acf5caaf85550,-0x1d08f4aa84dabcd253f746632eaa92f63dcdf0f8,0x3e8ce32135ccc802038cfc933a78b62e2b31694c,-0x76d49fc64a4b3748e55fcaf715c4ca41994e2cd0,0xc82fb87b6a64e40553b148db5cbda4b790fe0140,-0x12c61cce9ae5274c82c2f76caff7e28cf9ac57ab0,0x192df33c6885f5bc7ec2496430d02a8d1836f1d03,-0x1e446dc57c6246e71248095076c1e9de783eafce2,0x20ace0098233867cbd7de1c6b5959cc9f0ea9b414,-0x1fb9b970bae17cd7fa9f6d93ed99d2061072b8dd6,0x1bba7b57ab3b3a245cd3840d339c97864c4f0de87,-0x15d2ef02a53b5dfc2266b4f48c4433d72af878014,0xf775122a0ce448893d4f1e04c21f7323e7ea67b0,-0x9dce30bf0420f4d0b805f4602e46ea5388efd20c,0x5a74e2c780280983faa848bc267e19b3b8d56057,-0x2e883fa082b98a40aad67ca7a425f9d4d5cd597e,0x156f5e81a698b721bf04aa12cdc199ba587fd184,-0x8d153d162328fee1b62fe6987c2ec2cc20709da,0x33a6b5b2a787cc7e9a956af35fa3a01d48c586b,-0x10c25577f35e24729fbb1158e1e1fe1420c4768,0x4cb8ba6bbc18690bcd18a7600b88e95df42740,-0x133d7168e8f4e7ec6fe31e778a677c5ffd5618,0x432bd8fc7d15c2680abad34ef3dc1254245e9,-0xca4205bca80ff750045287e816cb627d96de,0x207aa62238df09c1afd779ef38b346aa9e5c,-0x46476e42c4dab2ef4c1c35d367bab0cf40a,0x7e018cff5bdb38fa0e851bd909d3a58f85,-0xb767920f390976ce1d89fe54baaa78a54,0xd31623f4632b8ca6e9b49dc92d06bf10,-0xb9909bdc2b7c4b7442e73b785af0a0c,0x76dcc1bc5a68b5a5fc0601b1a6bef1,-0x33e2d9ff48b263e03cc001ec1a71a,0xdf58fec390084ae4604055750fc,-0x1f6fc6479ce0d96dd0085c508e,0x1b57721ff4a17114e2433e0d,-0x477bb22e43624c759b000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 24 47 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 47 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 54 indices rho q4 m4 4 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 54 indices rho q4 m4 4 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x96193b271796c9fa8db46c980262b81700,-0x130da4da02c42635a3b6f1a023ab939a1440,0x12cc8b294479c53a6184780299e94bd284280,-0xc012d1d18b6887c1a67e2442ffb279bed4010,0x593b6a48fb9b20100081646386b12c4f43cfe0,-0x2024309f091ed25a7794ce936345c73250bf760,0x95777e98c25b1e6e540059af602e870331a2e60,-0x2404dda7f624f89c8cf0471481822bd104d05e94,0x756d7628d8b70d6d40ed115d2759ec9b71fc86d8,-0x1487965fed110467194729668b5a0681906186ad8,0x31d482ba128cd2147f415d2b9c57c56128c7b6ab8,-0x69e0bdd6bf94090bac226f166f51eb54aeb2bf1bc,0xc64fb29b0c73366eed549aa3670eb7abf17e182f0,-0x149402ee2d0b4627ba5957106e263acb55a4ea8650,0x1e6b228dc17342516568208be60629c5c420b231f0,-0x282c300cd7da167ca749497f246d703e9969651aad,0x2f87387675b7b77161893aa5bd4e969695f2a9d64e,-0x3279869867c3ae6ddeb2d75b0b71d8dc59a654cf9e,0x302f337e765d3f85bfc51b69d1d6ab365499367606,-0x2961f1f835ee2f0a52575719e67e2f63c9d6ff75e3,0x1ffc461d0dd81efa4aa73d7a7fd16999018ac86d1c,-0x163eca2f1277cd4b38a8036c990a2e3db4304dc0d4,0xde973cd391313cf32a135f0a798edc1ab51f96f9c,-0x7d07dde73140e82543be92de033e42b02b1c8e93d,0x3ef9299b6f73a9d8b3e3ec514258ebe5a5b114302,-0x1c60509e60d62d51b0034021ea07986a54f1f723a,0xb683b47f1c84d54460617803bfd81510f28a0c3a,-0x4139b4cd4568d573d4242fa970724edbba28f09b,0x14a22c998a7213939c8221124fa5e18cd279f1b8,-0x5bf7e54432be2a1a9c6d5895146f8baa1f04c48,0x166bfd6b97acdb93c70c6e14265f950aa568578,-0x4bf922481b2ba5c2fa2e43f209fff8f645b11f,0xdd98b6aaeea2167798a3d1d3ac3ace98ef952,-0x22652560689e58cda8a170aecc1bc981a3c52,0x47c1e6e1fb60b34695515f1043bc0777c2fa,-0x7baf94aac68fb3a322d774e35a2848a29f1,0xac7bb3c848cc0f190b6e715df38a8b749c,-0xbd6df487a02e0a78ada06752268882ff4,0x9e217949a9db3089c0a746266ae7b8dc,-0x5f9c68e05263a5d002a43104e047063,0x271af0d445895c1a7d0736fedc0946,-0x9c3eece2bdaa329800c82dc947fe,0x142b40de546f563cf8aec799f4e,-0xfd76820c331334a23524b9c5,0x24ae4bbc037eebb1d88000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 24 48 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 48 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 54 indices rho q5 m5 5 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 54 indices rho q5 m5 5 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m6 : List ℤ := raw_ints% [0x0,-0x122d0e29bbdb42755728d9266849f44ac900,0x24859f652e53d89f238fa64fe184f2f3253c0,-0x23a456ca997dc1dd60952dace39c158f678380,0x1681baf7191760e4db4344d5c3909c0278f3a70,-0xa5648a28123b4fdb26be5ffd3d6195d9f82f520,0x3ae18d010cc8e0744b99ecc5a9d90a8eefb88e40,-0x10e8d8fb368e1f8292a3cd73eeac47f34fe97dc60,0x406753e4ac63d4e48ae4da992a8c456c013966a8c,-0xcf579bb5c16c0791191d66fa3f0d9639c2406f1a8,0x23c8ebd8835ee5d711f7d46d9d1c6aa5a38996a630,-0x55b764eb729f3701e1182235df037a0527ad7fd778,0xb3aba90f95d4764da26560168a53dd9fb113d95b4c,-0x14bdc4d99180ca9e006e207c4f318971becf933a310,0x21f1fa821f591e1d852ae0814f23fdf71e8b8fed3c0,-0x3170fd6358608be085be594d6facac1eb41869e0770,0x404eff721bde16358b52d4d6e2c94ebc9b5387f8d83,-0x4ae5db1ab8d423854133012d4c1283bbdd6f84d3d12,0x4e430a3e214ac4f23555f9292bcc0aeba8a18b43e2c,-0x49781a510a499195a28c8a0fcc141a729ac91441a76,0x3e0372c87b7c4629dcc25cb8e5f39a5bed8abc7ca87,-0x2f13fcca7fa8b68f33fe226957b58a2a5dc276140e4,0x202327e1f97cfece5a17bb265fc44b530c82a8e1910,-0x13b67ce8054746ccf84c570b1ce6c0e6613af28fc7c,0xada184578f9534f11ac12acbd2b4b1f79c46c93727,-0x55a229bb0fc1b749948c6c9883590bd131b2d4e09e,0x25bfeb803af7550cf5be1a1e9ba47181267ca1b9fc,-0xed4ae32a879d356a34a17b87e4fec14734deec4ca,0x52c8974b8e34c5315143d5883f2fd9c0e848648db,-0x198872e955b7d0178b6bd70b6cd975f240c4a3f48,0x6ecedfddd9167dd5be3203bd39654fc9279eb840,-0x1a434653ac9f709b121c18842531b5c18876e038,0x565c602ae4699d26cd70491b09d8e9561df8789,-0xf3fb7d8037ed57a7955019ee6f55189b4fe94e,0x24993f5051dee783130205634e370319d8a864,-0x499a6f3645a8fbf2d4a6ba969e8bbece8588a,0x79ef03aba20caa291ac05b0a912890138f65,-0xa2dbf3f29538645ad6bc5126dfced57af64,0xaa99ce6653c5469ff826c02f358c42d2b0,-0x8729e69d97d6b28f497597d5ea1febbbc,0x4d1868cbe42c0fa29576cca597722c01,-0x1d86093a5c82dceb7f9b6fe9111969a,0x6d68c57276427dc2e729fe5c15f84,-0xcf1656b65bfa1405194076dd0fe,0x92d06e38b9c5d6edbe024e4bd,-0x12d0ed08d0c1a89242c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 24 49 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 49 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 54 indices rho q6 m6 6 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 54 indices rho q6 m6 6 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m7 : List ℤ := raw_ints% [0x0,0x23374b70dbf8d0c358df24ba6a0f4950e5700,-0x4605ded1c293170fdad51048ca359009406440,0x439b6819b9b3052f7e99a4da3c14ece19d81280,-0x2a39f0dc441d963a7a3a49857f4519e66e6b6a10,0x132d7f8cfe46f0541872e6e11b85a3c2f008775e0,-0x6bfdf8ada5192145382f13b1650ad7e25983692e0,0x1ea6a43b00135612519550bc119230912a424c6d60,-0x7357c4a8c9698feba0257ff0d85033f12194c58494,0x16ec754228c5d80d10118e823a2773848d66b734858,-0x3e81286f216d78448634a67d7c41a5e562b48bf61b8,0x93c8740bec8ab90a3860f76dcac19aeddee730b6a78,-0x131a773eceee59a520fce20f3e041b9bcaeca3f4a4fc,0x22cd92a85ebc150e700d564e64688c291c671e509c30,-0x382881e318ef3a61164aeb7e3a5d2acdba08b4e7c390,0x509c601855180d9d662d0949937a396ffcbaf69ab030,-0x674956dbbf6e128f1312c01c8580b931768e85a5bc6d,0x76712c282fe6d38d5407f15356447e7dbad0edf3a6ae,-0x79cb36c6d778ae064f9566c907ea8d99382ecd229ab6,0x707483a6e5b7c123ee580de562a3261d31a4c0e08236,-0x5d4dfe1a57c3bbbd6b4617764937e9c57d01f904e8f3,0x459544c6f34975adf11d47c21d4f9a97741c1456e92c,-0x2ea14985e79b30a4d00c58252dbd5d92805e8ef3de24,0x1c0ed484146b11297ce2df6e3147954ecbaa696fbd6c,-0xf23c1a9b9926d63a09985311f19670f4cf4629d243d,0x74ff78f70d1d78f6c9d1c9435846156df66828e5152,-0x32762dd473dfd8862bd6d712469f89d12fa42984c42,0x13605db808fd5a1ddce7aeee46b8a018758ee09dc1a,-0x6996cab5245f671d58e36c1c7213ef268351a78c6b,0x1fc0eacf06b9e15a8693e4b22b5d66b1c0d52e5398,-0x862c93940a9659157d27c0f0e8d85957419c5bc68,0x1eea2303e299c996ebf29213776e2ec9e39e09858,-0x62a68dc0fc9ef79b79df7fdb0423ea6783a58f5f,0x10deb9e34e0b8ac3e4d5e63166b9c9eab61a6752,-0x271fe26c3ab14b2fbb45dbbe31e1ac034208b7a,0x4bd515a54c751e852eb1555185c006b9f3c5ea,-0x78b56047cb9094f4b2f21d4b07238c1b716a1,0x9a5cac57eb185ca91a4aea972b4ea3b6286c,-0x9a2af20842881077968cd0b9195fd77a8c4,0x73ddf64a97c2ae9011d69d7192807393ec,-0x3e4ec4fc589ef843fa2d4a2afb10e1363,0x165344d82c76a911a2359eea18636a16,-0x4cadbde6d771475311f4a9fac12dd6,0x84eacb422cb4bf57a8ec52de778e,-0x550415ee5f26a63078f1945cf5,0x9a62105feef95a4b5200000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 24 50 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 50 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 54 indices rho q7 m7 7 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 54 indices rho q7 m7 7 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1]
def r8 : List ℤ := raw_ints% [-0x1497b6140ecae2340d4c400000,-0x1d89adfbdd7a99a8fd0a940000,-0x1423eeb43e35575a6b088c0000,-0x8b04cbe62174b5583ae653000,-0x2a9b11d3a1656847066a1b400,-0x9df9d627029b54226b8bc500,-0x1cc46dfa035348c21b21f7c0,-0x4390786cd3eb840d1b04ac0,-0x8231c7f93b288d3158af70,-0xd06813b033b2925c11830,-0x11786929902340b7e0574,-0x13bf0c171248426e1a24,-0x12dec185613645e3b21,-0xf43992e078a3a80a8,-0xa71104352e34f246,-0x6059f8499082f34,-0x2e979a45c070ae,-0x12bb9e98b4060,-0x62fbce17b4c,-0x1a62d9958c,-0x588fd3d9,-0xe0e688,-0x19222,-0x19c]
def m8 : List ℤ := raw_ints% [0x0,-0x443b222aaa32147a7c3057292d7d9e0cbc8900,0x8648f47223842efa531c73e751a73a8bf83a3c0,-0x804c9a544dce6d86b7355371eef3df06310cfb80,0x4f4747025bbb4d1054b56a8ecd96782af292d4470,-0x239cb673c3bfa87119a9caaac7aa4f33bc3c9c9520,0xc64af7fe1062fcb6b06dd0fcee28f93c92bafe8bc0,-0x37a2ae81cbc154ecf776fd6db40e0b3ef2d38b98560,0xcee6d5ef63b5d1812ef985aff72b921b05062bda18c,-0x289fe4b59f740d622964170c4720bb1f1f72ba0131a8,0x6d65b6c8a9be3a9654b52615346a938ddcc29dedb390,-0xff5d6c799242092a104c476b38f74051ab9365f491b8,0x2094193b4e8a92ba4ed87584eee4eefd972ac2b35804c,-0x3a8dcb8a4356f04ad8c5413aa1553e74d2b4148d1c9d0,0x5d2c7dc92982958c738131527b5dd7ba0c023826a1c40,-0x83d59057e6d032892fcb9bf44c747c4b51005f5b91bb0,0xa66e46312b7a04abaf7270b54adfd957e5371e64f9b03,-0xbbf2e13681be93a5ec65ec77a8eeb3b4b5d8a622ef992,0xbe3a7ce0b1a9377e9b7cb96fc1110048a8ab1a9f65fe4,-0xacc8c7325a5b7570f36b062a1c0723b8a53268794d2c6,0x8cf1609d63021bf440b8f2615fc1e33cdd2de0119a447,-0x674569e67bd0d16328954815372e30514d8b2d2f2dcd4,0x43f2a3ab4c3e4f1bbb029436e8c5ca3ae82c3dcc594f0,-0x281cac42072246c42e53fb5835564f4b60c2cb85055cc,0x1537a47f4d26f497b45ae30b2a530e48108e9bf617237,-0xa097a505948bbddf9d51750b70b8b116f1c6af00076e,0x43c60c2c124a51d7aab03036e920959e955012d45e94,-0x196fe0b6f415de7dfe0fe2dc6a01cbb097a8f8ee220a,0x8754d78b4554b9b0b0e70f98a6d74dd38cb24b8a2cb,-0x27aec149eb35200fb7cf1822b2192aa1e11372d6b68,0xa342dcbfd17a3707055d935512cde9d6eab1e5dd40,-0x249127d9e92893c7e16fd1910d0ae738000fedda18,0x713a8be250f679d742cb91b279145715bb526b2a9,-0x12c033b97439fd98f4c7a3db2e8d31ffed7b1f36e,0x2a038cc1824fea12f10fc2da4b5e042e92a17e4c,-0x4e772f734906dcde3b97a5521d87a3abcef655a,0x77fa448bddfefc2c195b08ea293fc4aa51f405,-0x92d8f89d0530022513fbfb481fb9281acc594,0x8bc594f4543f5186cd20e6192f7395aeefd0,-0x63992083700bc5986d6dbed98aaf205de4c,0x3276ef1a8fc686e368e4f29f6dbf78ee51,-0x10e82a896fb0b097409742eeb4417c42a,0x35c7f04f0f70900670716efefdf61ec,-0x555299e5810a54c1c649193e3895e,0x31375db545793ac453740eab06d,-0x4f24939e245ff7f98b000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 24 52 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 52 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 54 indices rho q8 m8 8 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 54 indices rho q8 m8 8 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x19c,0x1]
def r9 : List ℤ := raw_ints% [0x2124290847ce840bc566b7000000,0x2f74fc4b44628469c32fb9f00000,0x204c4a7c18405dfbdb44b6bc0000,0xde79793b19f47e64581a24d4000,0x44068be4b19dbf1cf617dd88000,0xfb9463898e1ba4e2f4ae4f5800,0x2dae272836576dc4413f1ef400,0x6af03aef84d9d3f8f5c965540,0xcd4f164e4df68afa990a0d80,0x14744632fff80dab916a3dd0,0x1b4d612b33c509bc8d9ea80,0x1eaff0e2886a23807ffa7c,0x1d228eb13750a598b64b8,0x1762de6dbe3689cbc13f,0xfd9bc997b23b861060,0x909fbb547626fbe0a,0x44f65ccdd39a8330,0x1b3c79d03dd5bd2,0x8c91aed6e2a80,0x2447823e9044,0x742a324ed8,0x111ed3007,0x1af4260,0x15f0e]
def m9 : List ℤ := raw_ints% [0x0,0x84329232a9c107ad509da8dfc8236238ad49700,-0x10194d07d228d9952c3e274b978b6f9f40671d440,0xf396678cbfbf6c0951e05b378adbc48a8a4d91a80,-0x94f1c62569e9c442daae5dc1369e2badc60ca55410,0x4230bd7efa96011c7d8f8ed41b5d247be6f619051e0,-0x16c83b81e63076cee192ada9f6632698f603b2779e60,0x651f69b08e4ba41b6546d0efa5b340894103897b8e60,-0x173b996eb86b9c987778958903967b3adfbcf4cf23294,0x481f6ceaac3198a096235a673e015e09e706d8f4f5d58,-0xbfdaeba344aef4eb68bb7f03dee14879dba37d96fac98,0x1ba3e49150cdcb38194a668c6fc23f9b33f47d367c34b8,-0x37b192fd092f0023c973e71f596aeab8ca504068a6723c,0x62c5caef2ce777032ea420f66add70021e488f6207b370,-0x9b0682116cc85196e8e58b5dd98b023df0e037a34c98d0,0xd842959dd4ef93041e05342a8d3be2a3eb57508d47bc70,-0x10d0aa95e5277e4093d751a0f979be52e4a54fc39669c2d,0x12b428657201460cef895e2eef4375f88fc70ded7a49d6e,-0x12a2e0f4fcd605a548a613200301fc18ae5abd7e56662ce,0x10a7974b04755a924a06ffdedf4af9ccc3f7ed941232f86,-0xd5bca51999adea95daf3b3956437c3606c0cef0fa46c83,0x99e47280ba44888a9f17dd05c1a906b7d46ef65e9cc7bc,-0x636da0bbc81982192491f593da2e0f9baf012fe54be574,0x3997f67490d5bfa345d0324aac82f324e4098205b343bc,-0x1dde11384e098af1d00e71f941925742a285706c4104bd,0xdd6fa588dda04eb1f24bd296025a3103ae0763fdbd482,-0x5b72b36d0d9164de15dcf61bc6a6443d21447ad25584a,0x218cff33573a795427f6dac8f2333d639cdd8b8ab439a,-0xae4721049098b717ee3279c7edebf647795d6e997c3b,0x31d434fbd75b66d89c3cc21df814957ff39c0e72bf78,-0xc79a773f7af4f2767f9bedee3eb483f108bf2bbe488,0x2b7541672826f9929718b00ebc974945809e3245738,-0x8291596751614cedaa44d5a339aff4cd79188b3a9f,0x14efa5865bc9c87fa5e53550ce7f382802dcdc4172,-0x2d5089b1dde58a4f7bf87dd640d4614a44bc037a2,0x5187667474e2f29a092b0098a6d262067ad2553a,-0x77b7174fc7f7450976eb24c558a57c05dfb97d1,0x8c318d0946bce3ff0e3414e7c90872f2ea0bbc,-0x7f1d55117303edb378b939bbe69ddaa14ff94,0x55d61b8e3ef87240456fa71de15db1cdfa7c,-0x28f469b642416add01555421cd8b9b1ede3,0xcd22837d22d52c681d240168a14892006,-0x25bf27a2f68113ec70e2665a7de18bae,0x36c66f7a085fe1cfd4a639e405a82e,-0x1c7bba61393847824e3289b3bd25,0x288f2b36e4d84162588000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 24 54 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 54 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 54 indices rho q9 m9 9 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 54 indices rho q9 m9 9 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x15f0e,-0x19c,0x1]
def r10 : List ℤ := raw_ints% [-0x1c3d22f17560fb3dbd1445eb800000,-0x28603eead02966df0e69f0c9180000,-0x1b6ee943e3e2272b55ef62b1b80000,-0xbc9e692becf0d32625e0b8f9ca000,-0x398e7872e8c2e906b155bb0569800,-0xd461c78ae79b40e7fbf506e74600,-0x2677512444ad43ab3adc603c7480,-0x59cbe491491e0a12ecaef026280,-0xabda5c38af70388ed1eecdd2e0,-0x110f5274ac5a541c0937af1520,-0x16adc8628ce6b6f025ced7888,-0x195f2ff39817cd3118a5f678,-0x17f574764d0fa504d8ccf32,-0x131c5bcd698786cadc9378,-0xcdb6994585383f6d06c5,-0x7446e3c025c23fce2c8,-0x36da6d23752bdcfce8,-0x1560df17e93289b10,-0x6c803b400f06b9e,-0x1b6601b31f4248,-0x552f48f3a3ae,-0xc0b3c5b518,-0x11d2ba5ed,-0xd28338]
def m10 : List ℤ := raw_ints% [0x0,-0x10021fb4228e5fedfcc31773193c48e4dcfbe4900,0x1ee3252d66eb5a5e228e1fff4c5981641dcce6b3c0,-0x1ceae8cb349a0c3fdf8f7346db0aa5972118600c380,0x11804d434ee394abe419e82b50de723e88d826a2de70,-0x7b229903a849a794e8a9808f894d4c2fe09cc01b2920,0x29ed31713882f22d20294dde84f6893845a59d94c6d40,-0xb80bd5537606707ee65878bb32e5092f46bc6ae768260,0x29ce3de9c45a66e89bfb0aebe979fd47b828f8f86c708c,-0x80450ad70198d220ee3090b74ced224ef19c6d8ccdbaa8,0x15121e05e8d4f1ac4ec1f685d12c7efbf73d6116d5b21f0,-0x2ff8f1e98564ff0323e44c4e7241a44366383d7c2dfacf8,0x5f700789188326ce03132323fd5ec4cb179b12ec3a8af4c,-0xa70c92703c47c79fe36c7ff0b1a3a2b260622ec71c54c90,0x102a82c228d878a912dbcd7514196daf5760d57d37c040c0,-0x163cfba95fe3dd8cb932f465100b299d5c4af5327f304bf0,0x1b44be6f5e555e02bd30ed986c642f40f585bba63550c283,-0x1de17bf1e2e6c9ed3ff4332d42d80f27e9865c61d0037552,0x1d50aaad9bf4bc407372a29008faf9c634a81d130a2acadc,-0x19c7c6d28a3b4eb97bc883c9d7ced702c23c43e841696456,0x1456085155953b9d58f2d9c5cc21bf441c5d265743115687,-0xe63ece1253fce005c140f3e388edcc4c2e0055bc53da9c4,0x9218b1cb052a215d0c4ef6bead952350f3bddc257b3b1d0,-0x530c138889ceb17ab86061169d909b0ed8dfdb12afe101c,0x2a3a7aea79ab3fa63062179e122ae35468aee20bfccd1c7,-0x132b361276ce653b9674915c636f3619fffa892450ce87e,0x7bf4a75b2efd29cfd53f8fc906791b5b93006a0353156c,-0x2c7518da128156a5c13c5c8b536c76da3a8b878efc3f8a,0xe17b06c0fc3630f933123987fe6bf0d4dc3c6f4e6dcbb,-0x3edcdc5d4d626f88f18115c61966c9f5954d1bbed7f88,0xf52d27507cb60881b664fee2eb9aa1f4abbc2e6bb240,-0x33e30b46ec22d76a87a0b82a34bf0dbda4ceff54bbf8,0x973f597f44aba549ced34363b7015fa2e47b93100c9,-0x177acee89a94c70e44d946bfd052088106d48d8314e,0x31153b962672ab2c6f42b0c8081aea529aebb009f4,-0x550dcd47c8832a999d986f639f78481edd5732bea,0x77e6d2e9fc03eee3371873cd725dc2aa769d2925,-0x864bc4fbf2701a2c0ebe110a114c6e198ad82c4,0x73f2635792bff798bf1d4e312ce51d939f5bf0,-0x4a287ee2fbceb5f0d56b568fac21a89e977dc,0x214ca989480134390e8dfa1322f7c3d7df21,-0x9bc09440ab7da8cf9ac5fe58a5f640eb7a,0x1a823d9c9b1883b76e0c22b213964d214,-0x232a722175e913cd32f672e77f50d7e,0x107ac0b6664aa7991148069ec311d,-0x14c79427b9db9361c6c0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 24 56 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 56 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 54 indices rho q10 m10 10 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 54 indices rho q10 m10 10 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0xd28338,0x15f0e,-0x19c,0x1]
def r11 : List ℤ := raw_ints% [0x10ef017fd03a629cd506bd6d6e000000,0x182dd77fd02a9f40d4ec0ce620e00000,0x10676c5bf2aadb28ab1f25b0b9880000,0x709a428bec911059fec36aa9bfa8000,0x224c6ce279aa20e9a844fb54adec000,0x7e4f038c0e661a81d927dbf60b8000,0x16d37f3ecad11ac6c5844085ce2c00,0x3527af6c3b949df82413c06142580,0x6572d3b5963d2de26b18280a4e00,0xa0a28d3bd6ea78368e5fa3007a0,0xd4cc58cf4bd1f7ad556fe8f040,0xed1fa79bea4487df00ee88758,0xdee73ddf1d3e246819978740,0xb0def4e898281bbce2b298e,0x76453be72899bccf178e98,0x425fc73672503a09a59db,0x1f0bd01b82ea1ff60200,0xbf9db7e4508d0e9c18,0x3c0473805e09e3ab0,0xeeaae1024c5ab82,0x2d703828660680,0x64079d3a6412,0x8e90819cb8,0x63ac3c73]
def m11 : List ℤ := raw_ints% [0x0,0x1f041d6d02f3d9dd19b9fd6f00e4cd3b6c280ad700,-0x3b4613e6aee8e216f9040f3cb68cb1cd29a6973c440,0x36f3b8564ed617e5a7e4aa4c77dc3b960272b1124280,-0x20ecb15ce3264237a070ee2843566024e44250b30ee10,0xe54618222f08c15ffb2a40f6c6ab4938ba8a4baa565e0,-0x4d3e62c756a511369d01cc014859a7b28da3b1307535e0,0x14f6984f9b1a362df55ccfd746aca0e0be81ddab0fb5f60,-0x4b576d6a61e099570d2d2045f3020d519aecd476af92094,0xe48670b52c971d0f4abf301a264407aec2b80366021d858,-0x2519357da4775875dedf8b859d283f8ccd9b8f7679204278,0x5370edf8969a75ced4466d5a0a0cae1196fecc08c2de22f8,-0xa3ee20adb11a4ec2bc1188810d24a68076017b698f08bb7c,0x11b3edd080b1b8edc9aa80d1688b8ca47d364ccf9ca9630b0,-0x1b0c0ef1718dc1897b43e095fa9db3db9017c8a5c0ff90410,0x24b238c77a908abcd12241f4df6a9f5a6ed27cd16cd56f6b0,-0x2c5be228aa7ccd62c298d55773a28b6fcf7a6f515fd9a8bed,0x2fe51c9d9371607da9692886e8b709d6613dfcec3bb3237ae,-0x2e460588a2937ab6419b1b9e3048c0aa3b5fc01fe8d8d1ca6,0x280d41b1c1afce5ca66c077d7ad18f0c43dbbc8ed82d875d6,-0x1f135e5e8dffdb7134ef204207503aebdc2650ce20c355313,0x159d6b91bf5199655621ae6570456196f7265ea5c32a2cdcc,-0xd78b6dda619aa761970bc3d0955a150853be4fca2f066e44,0x7840cbccbfa3ac61ca32a464568da918a1b261736f2b2f8c,-0x3bf66b2f0f709546ed9e6629e6d949eccc410989e77b353d,0x1aaab182c1eee6f4a3dc2daae47f6fd8095c57223664bbb2,-0xa8c5b98a378a1c1ba8a463f254c8d9d54c9e23635e9d292,0x3b2d59582368b628bbc53cf38191081f2b01f179503e29a,-0x1250ff4e13da8741da5c45fcf973d267ad6070479a5370b,0x4fab7a9d574d040d8ea30baadccf5c774c1492dbc08058,-0x12e8828383bddabc664de854c97dd9adf5181e8a1327a8,0x3e3b1a903aa2b7895dc0a1419ef0788fd74bdac034b18,-0xaffaeeae467aba784d8023a40e923eb3304297215ddf,0x1a7225adc8db633ba23cb1214e30a57d197f865fdf12,-0x35627353f9190a4941ac0ec89326dce73b2c786320a,0x5913fa34746fd736f209fedee0073a817dc936148a,-0x7885d7124bfac70584f4db6c5e768b02d18289201,0x8110ddd5cd6579d6b61ec258e954d274350fcc8c,-0x6a0f3e6e8631ee2aa2abcdf4c0c763193bb1fe4,0x4037c6cbd29e2f612cac95c7b0b23dace5a08c,-0x1b1f638187b2e5886cc5a0068f3ead935f063,0x7664641a073e959f6cf05e0c7b26777acf6,-0x12a056dd5a93abe64321c1460abdebe846,0x1693a0075c41cd705055d49aa64cdc4e,-0x9881ac80fa7bb5dbd8b65c09d0a55,0xaa490462fb32b0819200000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 24 58 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 58 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 54 indices rho q11 m11 11 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 54 indices rho q11 m11 11 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r12 : List ℤ := raw_ints% [-0x8048634e605e4444e453c7ad840c00000,-0xb6f2ec155af2d7634a6b5d229027c0000,-0x7bf445e0d6ebb8bd9beba893f86040000,-0x3519ec20d1557710cd4ad6ee2952c9000,-0x102607e1c184b24a723311d2254d95c00,-0x3b5d202c560987f9cfb1dc0d2316bf00,-0xab50248fd390b1474866353e547cb40,-0x18e11ba34884ff2fc3a815d76e86840,-0x2f5e5d8f20d662cc8481301d20e9d0,-0x4acd4985085b1bfadd753df9ecf90,-0x62caf2490908abbd24e5909d567c,-0x6db5e59e1ee41fa422ec505df6c,-0x66bb74dadb7ab38ec1defb46ab,-0x51282048c086d34420d4105b8,-0x35fe0c33ed494cfd86a627dc,-0x1e1f4a79869ed56e1fa7f0c,-0xdfdfd14251c95b74b9ab2,-0x55a6bdb8c230b6ffefa0,-0x1a902116c4fb33a7500,-0x685bd7a33839f3204,-0x1391df9f552e8f8b,-0x2a41a15f48edd8,-0x3ab613536ab0,-0x27a65ce584]
def m12 : List ℤ := raw_ints% [0x0,-0x3c17f90335b8761c61d85b0711bb4da3218d9500900,0x71c5fed08af4dfad9bd729da049b3dd07a88c27cc3c0,-0x68789be83a0113e23444a7dbf458843b5f47976900b80,0x3dfb290e16e36a74e4711e9ab68d45273168f3a1aea870,-0x1ab46464ed13850eb09d39b01ec74a93235f0f9b597ed20,0x8e773e0fa2f28a41c79b81b1bb071a6a43d188f42d01ac0,-0x264105adbb0e314b7e75a43ad6aac9eef677252fdd7a1760,0x87fc316522490baef76abb04608d68a61844ee3ecc16a78c,-0x197d78e056cc7f5f218eefb6a5e7d5082079b9b1ae011cfa8,0x4171a08ad253cf4b712ec95c7bec866ccc31f9260ba937b50,-0x91717b51d74784e6f755ec10e7f2ed3ee71943c4593657e38,0x11a3bfb8610d21c33045f6bf55b6bdbd062bf363ae5e2c244c,-0x1e17ae1b195f5abfd8520eb1584b47c087df3eeb6c79e7c150,0x2d5ffe33d870d0c5d42d79b77faf43e455ee8e31a0d1fb7940,-0x3cbad04b43ed1fb3c24d8d5e71e3171fd6e6aea9a63a5a0230,0x48621d89993b18f354126e940f9569ca172b5262c110873803,-0x4d05043c4cc2e85900d0d71ed6c32b8337bfff95e1e654fc12,0x494ae6c4a41e03adad464c4fc2951170ab694ff2e85c20db94,-0x3e7261e2df7b7a3417c79f4906e7ec5dc285c6bd7f4cc61d66,0x2faa1e5ae3ef3900af1b110fdacbf139215bcb43f4b2f50447,-0x2097b7819b534dd7cd48d43026687da32b822f4462d7ff9134,0x13f484134769dc96f2903d740c46ada8ee254b525cfca701b0,-0xaed8f6f23a35fde5aaa9fb1eab5dd0abff4849e9cc1e1a1ec,0x55815b1b37e479a7230c0b35535a0ce6322122b961c5f46d7,-0x25421e946d07f9222bdf45430b70cf15d2e4c89fa4979cc0e,0xe6ce015ff5869202966145b5e83f5aed4e3599d3f3d18d04,-0x4f1f2701afbf95fff3708a820c33c8517823ef10ad5fef0a,0x17e9c25f6a23f10b148226eaf20745b8b3321385da12b0ab,-0x656cab45fb6ab7e258b1b59b638d0080818999d82ed86a8,0x176f99b0a59b7ba40151aecc86c491cb83fd9c4ce928740,-0x4af7846404cd3b6156b8c55b3c5be098c655f6c24c2ad8,0xcda4c43922e1afe93e551437bb26e582c74b596b157e9,-0x1de966a8af3b36f4520b629a7bc3767b0e68e6756ef2e,0x3a4bd863cdb1953a78cd9993d8edd8276729df4414dc,-0x5da528eee684a624a53b001aa49ed56b4fbd416ddfa,0x7991c3f9eb34586a0ee1e4d9efd004fe0b6d1075c5,-0x7c6d5586bf7afe05c8315275857cbff004f436874,0x6146dec0af276a2234916ab5fd0b9a297d7d5510,-0x37bb680d15f5f57d6127f86e3b1a3a3c3c1f6ec,0x1620acc58626e08be2756a31c7a9d46ecb7371,-0x5a163fd309d1bff6573b91d7681a9879a14a,0xd17fcd87ea6cd23f3fa2ac4364f096d17c,-0xe7e739e4f882f60fd9d403a42e584e9e,0x582ec018f653fdb813fbd4363316cd,-0x5730eb258c31a2f1bb000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 24 60 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 60 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 54 indices rho q12 m12 12 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 54 indices rho q12 m12 12 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r13 : List ℤ := raw_ints% [0x3307e961b05cf29182ee72ba31091000000,0x48b26f9f113689f29e9d280c74797900000,0x31320ca75549c63b5ea318c65fca1b40000,0x150c1e58c1bb1f99d26576ef3242a18c000,0x66435ce9916baae4fa31fb8fb5ac384000,0x177558761d8077a66a178f59c9f2713800,0x43941709c5b511a978cdbcf69c60bc000,0x9cb9a6699600ebeaabc1a8be497c7fc0,0x129c1f430c9e582c16ccac45fc013d80,0x1d516443e9b6ed436c14530e6527ef0,0x269e526f06392d3c92b82571a4a840,0x2ac24f16e2272f6a337cc4028fa14,0x27e7ce028b77d865f00b5d0f5ed8,0x1f67c40768ab018ac2eec64f9f5,0x14cda74831c699b618238ab900,0xb8c715dcf9535d13729a1554,0x5556b104cb611238f6c4770,0x206e1d257cc7225089b4ce,0x9fa450fd5102ecccee80,0x26d36b185e3d05752f0,0x7324285cc099ad278,0xf50ae2af3c0ed95,0x14e40c97a71a00,0xdc60e802aa0]
def m13 : List ℤ := raw_ints% [0x0,0x746e7276381564d6fd93305db25ae66c110250b11700,-0xda6e472f0a5b8f6e6d839034a264bdbf81da3412bb440,0xc6b325975555b4ce37514c2a76c8fa2aa76da23f952a80,-0x74c19c76e4c3adc9895bda8b765bb01860bb6961d077810,0x31cf4c6b10477cdfcc476c170b8ba15dce2fb148cf04b9e0,-0x1070ac20a80e8df911a69a7c5255a7516aa164575a2a22960,0x45e566aff40fa45b1c7b878286c8258924377ed6c7c655860,-0xf5ceff08c1007d1aca95ccb321ed54f5d5cc54498c5a4ee94,0x2d919d93f5cbb3a77fb6a54b6a37e423fd1042c4db24714358,-0x73aa9eba875365500a543737f5cea5a1913c3e585b228d5758,0xfe0cdec0a497754a8fe6058605f3d0b949771eda0af734ab38,-0x1e7086da40ed0350980a5e38c39027e50dc27b5c9597a6c58bc,0x3347e0844d6434468a427dd6701103cdc8115a1860db0d453f0,-0x4c538dc160447ccfb0e4a19f2a942cd15817dd8ab189159fd50,0x64caa31dbc34f88f8cfa0c5f7e2c2b09de16e4e31f2f6a6fef0,-0x7678bfd05dc326e8937723ef0fb9dec5b1567da4edfe7e243ad,0x7c40b717172947dbeeca38602a28669b9064bcd82d4f73879ee,-0x747af55995e099fdb9ccfc3de59da513d3be662495945b9893e,0x61b55661a7dba970a7c84fee260391edbd4c91db44941da48a6,-0x4960d80966f1befe9724e621abfa45c28231405b1921b376aa3,0x315568af002e50853279eaddf578827a1283d3aeffabebb575c,-0x1dad0e239c4937cf5fd239aae3c830934ef520f80c443a26694,0xff43035a819b06ff66fee90d4b95a814625a33b8df0be93cdc,-0x7a6fe73ae70883ee184c6b7e64783f328c417d824a02702bbd,0x344732ef9a185ffeabf2de98a0624d990c31c1e5c6ee62bb62,-0x13d00a59c9680fc70823e45b4c510a4d2f0c7a133f37442a1a,0x6a4043c1f650eec594d3390cf2e92c79cd5426da3f8ec749a,-0x1f5b7fab3d5eb61108f87a4c1d816fb659beddea9b30240db,0x81b02727ceddb4e9db8e5c83c56c45d7678acbb105487238,-0x1d2cc9e9f265164c37c2cd8aa255b6aafb6505f40f54e1c8,0x5ab2ff7e5cdc05e47a22dd357ec0b3343103cfa1666e7f8,-0xf152385803ed874c25d4b8135f2a3a2a5451822fdb2d1f,0x21f846959eff1aaf209162e07f1b56eabbf5ca0a86ddb2,-0x3fe864458f5fe5868f4a65f93092aba074f1e8d2b29b2,0x62ce63b3c67890231c367a315b94140a05a38d485e5a,-0x7b095d0608a45fdc84e4f4ece86e729958cb945eb31,0x785065cbd7e9145a4a9f601b08224fd80f37018adc,-0x59733c5b7afc377c64a49e43082aa20ef2eeef7b4,0x3077b65fe28b3868b00d1f2eed71d90eb14d9e1c,-0x121479f6b61f1850b94d45f8b3d51d8da4f98e3,0x449d11f99ed51e00ace8a09fac98fb88d9066,-0x935423392c7cdaa09bfd7ac5d8c5f3bb09e,0x94dee838c2a8347627660c94081cc946e,-0x32f94ebfb8b80961c5471dd03ea7485,0x2ca1c5bd899b96ccf88000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 24 62 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 62 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 54 indices rho q13 m13 13 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 54 indices rho q13 m13 13 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r14 : List ℤ := raw_ints% [-0x11ba2c07381a3ef2db5a2e43c56d228000000,-0x193a78016375174c5e9acf628e0d253800000,-0x110dce6d8ff706d50828ea1313904b7f00000,-0x74999e3990db90bcf742b4a48224f76a0000,-0x235ca22ffb9ce16c3977c563a4a4827fc000,-0x819a4b174ab6aabf82e2519741af974e000,-0x174c5cb70712aa473845ad1c302f56f2000,-0x35f07975b3b40d918cd298083c14667800,-0x6648761d0aff7627678aac028f2b98640,-0xa0cc35903eef73df2923a2a202a5c080,-0xd35011836b15cdf9a45aeab10af9190,-0xe95c2c6c38946e4fbe651f1875e640,-0xd926dffd513edf92bb636e50bae8c,-0xaa561f242970a2123cdabdc4ea28,-0x706a19611acff7b51faadca56cb,-0x3e2423276a5f036f437a40fe80,-0x1c8f7a4f4c30baa107552a00c,-0xacae8adf6f45038395e6490,-0x34c7c77503296533ca7032,-0xcbcc0cfaed8b50521700,-0x256cb06f1cde7701270,-0x4ec0e83f38b0eaa88,-0x69efdb11f21c02b,-0x44a05eaa6d280]
def m14 : List ℤ := raw_ints% [0x0,-0xe195fdc50ca973608b4d2db589901e7160f47c571c900,0x1a37327b1beaf7e405161efbea6641cdac1eb13fe2ad3c0,-0x17a14a45d2f512d7fa3b67a86a3c0c2e9941f56817799380,0xdc145461551319b614e78fb1cae8765a93d5ccee190ea270,-0x5cfc1561b7b5a367bea316a3e788d62db9a2fde990330d120,0x1e62ef269f39b3a4db0eb9146b9211c467a402dbedb8c71440,-0x7fdf8a09a7bb338ad5581d2c78d33102dc2f977bf1e7079460,0x1bcfb523cca483816ff239f1cff966e9488f56a8b2f5f48068c,-0x5199a35e21764f556c6146fe8e96700a51e66fff150e6aa3ca8,0xccd07ee81cb6d611f6e19546211978157486162c6c85f6a1fb0,-0x1bcad88b622660caf93835f39778c6dae098d7d68fe6fc776978,0x34a58a83f8e76bcd1d44f82a87a6f1404758c1a696ec42164f4c,-0x579a43090d1ccbda7c07b81ba8075f6c27a0834b315d10499010,0x80badbcf649041a2fa4f44f6b1b7809e24ca08c911829e0b95c0,-0xa7c0e57d1df89c1c68cd530e586ec12ddd08110f458bf968f670,0xc27cc806445bac3710cefc94f5a7e9996fb0a575289752808b83,-0xc916609129f0874a8e5010f2d3e12f39a5fce2cb20f5a50a8cd2,0xb9bba21bbbb41f217c64563186d25fd6318add8815c7f186aa0c,-0x9969e23990ae0bccf5d8b3c80729cf1f0b1308b868fc7de2eaf6,0x715fc35d59e7a832c70cb6ecd7aaff4e4899cd756d42b104d987,-0x4af469a8bf348b0ac97547b817a2ae554b6b6b388cb016292d24,0x2c4dcf73c52b5f496916f10109cf5342ac53d24a408e4bda6890,-0x17626bd869da62c9c83bfad34bf52e55467c0a51fcbad119793c,0xb00a34c59442efac387e285d96801b17d648a469b5db91ec567,-0x49a8eb6a7c2ea5bdcc27ab3954bce4a728734043105da66cf1e,0x1b53e210a6d21dcd9c9a81a3125e4206368ad00a6c9b8f2395c,-0x8f4b9a75cb72a365f4b02c398658f51cd1371274e6b81cd78a,0x294bf37ec7b55b0801003abe565c7e6aa48d6ddef01dfbf69b,-0xa68b0e95bacc3004fbde9364a5c729ae3dd1c4287da1084c8,0x24798fcd93d681e41feefd2b115f77cab886c0aad04fa1440,-0x6e321d3c7ee1d09e74fc4ee4d3d73768d99ffd69c6f2f2b8,0x11c5a790c25ef229271dbb79c0329cc77ed7b260240f7009,-0x26bb4a6ac2e297fe1ef78e1e0b67a9660b09321c360e60e,0x4652f4fa763e9222eea215a2e46d82b12b6bf06d44df04,-0x689eb4509747df457f98381e9b81f3b25c44f602ff68a,0x7cec71ec723f25faa9df54b27d48f2655b06c09475e5,-0x74ab969c6c495368f4375ac54e70809773047bfe0a4,0x52741c2fe3f7b25d1bdcd2d6469451a1df6de52f30,-0x2a3b6efec40a3b787ce615cf0041d453ad66e397c,0xecb2848edfdc473f6773ae0211f793df4c0ef41,-0x344da6cb9428dd7b9b5b70e072f9363e57e49a,0x67a45e8e67d97dc64750bf9622045d40f424,-0x5f8f5d148664525be69e5ae1705b39f9be,0x1d74e1d66d27eb4c6cbc8e55766e117d,-0x16d718cc84aa7e0e5ac0000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 24 64 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 64 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 54 indices rho q14 m14 14 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 54 indices rho q14 m14 14 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r15 : List ℤ := raw_ints% [0x58532cc8ad939de8348961e55ee0b2a0000000,0x7d95903d4ef245d7e7781751dbde588a000000,0x54ceed7a9e2bc3c40b833977a3a47cca800000,0x24337faa070d235b60922d0945115e9c080000,0xaf747ca6f432e219b8ba79d24c9a1b7180000,0x282389501d3fad6bccbbe8c97007da8fcc000,0x734985354f07379b583aa92c22709b428000,0x10a7ed78c2d4d78febf8aa6f9bcc7887c000,0x1f87c0c8c8405726cb8041aede57a7b2000,0x3179abf640606dbc77972ee9a3e2c9f1c0,0x40e21710c0a9be9b3db75b436995ca180,0x477cdd977957923fe064936330fc4870,0x425a16e4ffe2d064232ef313d4a6440,0x33e5db4f51f8c316ce711b3323b574,0x2223cb95fce672478b4a2959d88d8,0x12cda03a100fb4e3b55dd53c6735,0x89b32c4dcd153d345ade83af00,0x33c9ab539f63874568d130ff4,0xfbdfe560eec5de731976f70,0x3c653b0779d4d1d44505ce,0xb01dbc9a975f30c95680,0x16f46ba7f7a33512190,0x1e8ad845080347c78,0x138551fd9d711d5]
def m15 : List ℤ := raw_ints% [0x0,0x1b5129badc8884f8b0de5888fba873afbabd9b0e8c75700,-0x325a268bcc35c72460c6d7027a46bb4b04d958b0cf6fa440,0x2cfb484caa0675f402714e2f54f86b88f9d3d2d58aa725280,-0x19f198e15e7e4c453a1334da2b9b8460a7cc1dca063be37210,0xadbaace7eb64f6a2fdfb372bd55bc45599f1bcacc5ee796de0,-0x3838eb7f4eba05b1fa57720ddc95f00fbac5e770a05036918e0,0xea3bbd2e6af28268e8fd6365b68a894f7d8fcdaef1520e69960,-0x326b5ebe204d23aba312e6683126e231261dbfebd984a633dc94,0x925cf2195ac74fce5a50b62867eaa8f8b72f58ecf1ce88730658,-0x16b57c123e5758e2ea9cefbd04733eb60e02bafc26a126bc0d338,0x30bef77a14d78c55ace4306789ddef9785e8cb7af712f5a487578,-0x5b422af09e15912d4371fc43f3e80644e4bce1c503ac0f42a79fc,0x960379bdfa5dc4d205bf76eae927dee2136dbc9347756a1136d30,-0xd9ad99b1190fcc2fd36fca4b417c99baf0f639a6b0f851d038490,0x117fad2179ae58efe68fc85bd8394c2c227f8a420d822fba71c530,-0x14038c4168f3505a5d07282302f09c6a0e7cd2d10ac9147c16536d,0x146736f4734d6d958d1cd1cbdf6836da5f5ce9b8b452e310e1662e,-0x12921a742cf593845b22b83a0427c2e3a53efaac60fdd2e70a0a96,0xf1b460ef3815f08649b1218beb1fd41b5251f1ceded4a68cb99f6,-0xafcbeddf385a9ccf1fcf5bea2342963b7528895e5e2ccafcacf33,0x724df0a0f947befa3d3c645b77bee5d790d793d0eb710cde7586c,-0x42654ee06177d32ba46b8ad4c472efd676de12098c37f2404fe64,0x2269342ef0c349c833369aaed78b5b22df17f3c15b213190167ac,-0xfe219339343bc372c57fd2e5b800ed85c46a8c1398db3d6d9c3d,0x6836b3e12d688ab886f83eb3fb1078df026a133a4a811e4ae192,-0x25d9bc59ecdf35f339f70664bc9ee45d4f56e18a7b1f19a630e2,0xc211e1b329016200aaa88835840044649431945940b4424cf9a,-0x369ddc1f0126bfe7b918e96a14755f49226baab9b1c1317d1ab,0xd6c6904294341bb24411ec46112286480e432447d32938fd18,-0x2dcad0f48a0e50eaad84acee0707aa74886b5309fcfe2f42e8,0x866f3d92154aff4a9147b655f29d445fa39a9c29eda7005d8,-0x150670debf6a601eabbb29391e000b5b297046eecd06d205f,0x2c54d033a05c7f30300569b38d83b412f95cfbe6984b9b52,-0x4daafad0f53ad1f2afbff41ec45dab5c34b42b2dac9249a,0x6f275ddbdf3eb6f69db587155ed6e3aa1a88dcc18890aa,-0x7f3bcd32b150f594a235be648fc0649167ab0d9c4af61,0x71726365d18fff8e5d3e4b5f6d542890cc9500e1baac,-0x4c2e1647367633473ebb25bff80b240b9398caf8704,0x24ddc3672e02db8d5480d13b124db63472f5e1cf2c,-0xc1ed0977dbc9efe1f681679f65f1803acb9aab63,0x27e6a91f6d2afc60958f817b668c87cad7db456,-0x48ee0c87a5d3205762ce6ce3332cf3205c2b6,0x3d555fe315f263f677d4eaf0bda5861c28e,-0x110465cd7fbf468116d2492671d8b2bb5,0xbaf6e495151405a05200000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 24 66 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 66 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 54 indices rho q15 m15 15 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 54 indices rho q15 m15 15 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r16 : List ℤ := raw_ints% [-0x191fbed7cba2caf7d11b73ce4c377ae0b1400000,-0x23b14b41c0770b84495251dc271addd701240000,-0x1814e7cb2da376d5ac2e60a40bea51dade7c0000,-0xa44f238c62d906e1c9472dd92544d5357e0f000,-0x31b7f0893fed4c3381624534b40a659b176c400,-0xb5c5bcd0e54b124026c4f73b1627857f47e900,-0x2096be407a3a19289a0706e5edc198fdfa22c0,-0x4b39f1d146473e84dccbefd98d11618a271c0,-0x8e3008f933cfc9fc2b969b608eb5c0f8a830,-0xdebc63b271f368fb57006fc4754c2192ff0,-0x1238f492a0ec505fe33be316040728098c4,-0x1409462f05e56ea930026b7f0ea993c4f4,-0x128df450604ae9a030c068f63854d8555,-0xe79d499d244f7aca53e9f9e61f35208,-0x97ee6f413821c4f4bf57352962dc12,-0x5369e4e10c2890cfd6c0b35acfae4,-0x260aa1f4e2372c58e4f547356df6,-0xe3fb14f23efae68860f1a09660,-0x44fa2c32faf937af6388e5534,-0x10735ffe3128a816ab4106bc,-0x2fabbbb03f9f93dde364dd,-0x62aea02f46ab28169968,-0x8226a7a87f98ef2ede,-0x524e19e9bcf81cec]
def m16 : List ℤ := raw_ints% [0x0,-0x34ed40da0b4881a1d6aecb896796602479cf5c6c30238900,0x60bb2d91bf216eb0567bb72a48a62f00d735223801604e3c0,-0x55a952075e7ab11ba7bcd4bfd79479b6a527efb7daf64a5b80,0x30f6bf5b4498ffadc211d27ee97491b02399e250665258a4c70,-0x144db8bbfa2222ab18acd14208a5daf60dd69a80029a01949520,0x6821d6631d28e9edebf88b26e87963503c341dac4c2a3f8839c0,-0x1ad96aa43c384c9584b1ae2246292a064b3c429c41a2aaec87960,0x5b895ef654c2650fb71cf96df0effa8654a5af4ec9d01cb3a0d8c,-0x106f41ee8af1b0acda7464188b2370a6449da1f2e8720a422cf1a8,0x285bfdfc5a9c0e93b8b37d9098639be3545d482b27750bfc918710,-0x55ab68478a9cd7c4d7723ccbbd475131906b50f590c4be1cf78eb8,0x9e899bdaa589439da2d3d06b11102e357e05bb02b1f9a91795f04c,-0x10180863d5abe3235aad35b9b0858e981348e2752e2c80e166c48d0,0x17108570222517f8c9b0c78b86181a78b235bfdb5c90550adcd0640,-0x1d49152236ab6430104b2542db5e0cb5a560738f0b7709e0ca838b0,0x210c773bf1df7b1b5e690cabe00d0eee068a73032f32abec8fbbd03,-0x21399e9167a953b2d710515cf873f4b6a8bc30a913916b99edff392,0x1dce1df136c18275bef3935506f87e66eff97b6dc6e49bf0732ec44,-0x17e18be4a168900b40740610835a81fe3cede6eb30b771a54431506,0x1118c851604dfa489868da7babcc3110d3c78601a7425c66a150647,-0xaef2ead1ed482d283f9cec82eec82456ca86e0c063d688b6087194,0x63e0f7ed91b1b0209a36f6d76e2512d00e4809de2c28bf52856270,-0x32d54a7c2552d7523073e030bc1eb171d21e6768a95b6c12478a0c,0x17051f554f41e4fcf8d98c2bd2891d511cf1fe6eeb4a019ce5cd77,-0x94099fa66a73b9194cd064063c9f93ab0f8ff12fac131e84289ae,0x34a3f30a46da738ffe1a1678ad3374c339952be41c06db5fea474,-0x107ec67dbf0667f3bbb41930150f805a9e349d0492237b46fed0a,0x48886583597caa333eef34761c7ac3b9584378c453f78bfcbe8b,-0x1161f8b529e2e13471198556bae2354d826d4f7ddd355a71b1e8,0x39b9ad00ba4076a4d6bdc13f0bf950b20bbcaea1e1719431140,-0xa4aa151023dbf1e3494c1077b7641869bb6b33c56e36f2ab98,0x18f88bd408ccc520b530f02afb6af9b331a453abec56e6c929,-0x32ee53c6425ab4676830c1604652c08e4ca207d90250151ee,0x561546a914e26a3cc7efefa4b1f55a17b5cf77de964cb26c,-0x767c200b09a93b495de46099a9d7bafffaeeebf2cc3659a,0x81f92743d41543886cc0bd0c87f5503c78ca6214cff985,-0x6e99ef974ff5c77a4b489038cd49ce534c421bab0af54,0x4689c9977cbf20ebc83e25ec5669a071c4ba18bba650,-0x203cc8af9f86e39f119595b61e8f47628f8bbe4638c,0x9f1348d80a0b88998347dfd48967ab8982542d291,-0x1e75f2c019eea86189af8e7fe68e31929568e56a,0x335490ec7be0c9160ccb31d09abf22c9f1f80c,-0x275c659ea6773e1fa53fd74a0908d0af82de,0x9d3f6a172c49eef1c3e288920d9d8d12d,-0x5fa0b8c47ad74d5e2b000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 24 68 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 68 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 54 indices rho q16 m16 16 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 54 indices rho q16 m16 16 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r17 : List ℤ := raw_ints% [0x69ee0a184e98afb90eecf2d3c9d5a4e994b000000,0x965fcec41fdcd2154e944b82c2586eaed3f300000,0x655f6271af957b1ff2791aa4138b349642fec0000,0x2b30a45b89e0ac083826bfd33724edbe3780c4000,0xd0e5c21b71edfc75cd5e9b735fed165b54e10000,0x2faeb9accda4056b0ce29db36feace3794eed800,0x889ec40391a0aca6657ab03f9399efc3d217c00,0x13af778a5186304171aeee49c14938502b7c640,0x25280b496a6fa6148bfd7f1d5e8e294ccf8980,0x3a1dea8d4f7e81e9cb84ba4648fdcda2ee410,0x4bf29c05e2563d8ba664a493c79619199300,0x535a8cb9877a6c42dff950b414a68da866c,0x4d08761bafb0fe30140bb1c1994c313438,0x3bf6fefee34200f8566d15588575d8b8b,0x273c96d7b907545a02adf3df45a77b60,0x157b4fbe2ca991d37471ed5155077fe,0x9c42806a88f42e498a1ebc7f60c30,0x3a525c84fec7e970001b3accf48a,0x11932c31b06da30477fceae1700,0x42c1be703955ec0f9e46e211c,0xc06d3b671408fe787b58a58,0x18be4a8a398884da180d83,0x20660e89c0efa6492a60,0x14501fb6cddca5b092]
def m17 : List ℤ := raw_ints% [0x0,0x668bada675dc7b298ff2aa5a38b35a46ac01c3119d44d9700,-0xb9de1db3ccd4188e2225513a34c49eccacdcfe4333ab979440,0xa3328cd5300af4db52caffd2644bb89c92f35218566b115ba80,-0x5c776d795991671e18219ac325605b856086aa5dbdb19b705c10,0x25ff2ca32a1ec32ed59ad6f58ec761cfc33e3bf85a702dcef01e0,-0xc1106789b2f353d14f28fe9487f3742c8ad57abcba88dcdd6e460,0x314d480c66728e243d276065b9720a9bafca4adb6399ced91ce260,-0xa66b620fedb7d0b341034e1eb66ee62382a9ac3a5d21b036baaa94,0x1d92d4908b9e19fcd4712ad1a8de4e0868b1c136b88469fbdf60158,-0x47db81f8fb2f147d27d7cab5516d724352f01e03b4de80aca782e18,0x96dc63558bf27f05440baf6cc5061b85bca3d7bd51ed89f016971b8,-0x114040994049fd9cd111de31c91f1f5a5d4dfb7523915936cfd8af3c,0x1bb0cc56a3c692c28944843a2682e7965c8e638cf903440f47084c70,-0x27335f48d35a7aacdc89b7f01cb767b4c4a51a8e25acad3a74eeb9d0,0x3124e6bf1b943c7059d9af5417a10c32b0d399df88760cd210f43970,-0x36bad619a5d44f96c3ff6da877f66c00c6d0a23a9a7d0707f79eab2d,0x3644cf8a393e3ca94f654cdb3e62dd8d0c0bb4f43039d0670f9ff46e,-0x2ffd0a5e986f3abd7ddc746d517667d1f7276d20bf281394c52c76ae,0x25e0c80a18f81db3741bcfdf3246561064657fde9d9f2bdaae6bf5c6,-0x1ab2280d8f4d5e42872797ed6b464a9daa1e79766a0c8308fbaf94c3,0x10cbb6fe50775ac2cd0abea850fc68f25b23ac97051dc9b513b4b4fc,-0x96ce2b18056fb15ddc1a00ad966d51b895926784b82be2213492db4,0x4b611ec5c71fb80cac7a36c0d9a282f09c33e5177a99566d0df5bfc,-0x217e723c8310640ea8003fa3f9e010cc770819e6825fa0435f732bd,0xd320778a11fcead5fadceafc211fd7b9be359cd0b910ef536c9242,-0x49812865c8eb9f6c21ffa3f63472d63593365465ec243ab67934ea,0x16860f7af6b4f1183ed52c911606e161f02fe1d1b5b2ed4ebaa39a,-0x60b7e8ac930071b5af862b75bef744e08b8101944d824c198717b,0x1699d93567801124fc17e7760fffa53515f0c97fb5f3558ca98f8,-0x490f4353ec47c89164f9f629c809ddb3ebdcd9f16f09f596cb08,0xca7be09899495ec0ebd09d4ce4d18704ad31ddeca5f5893acb8,-0x1dc51fdcafda194647423f66db66ddce2bee0b0968394fdbf9f,0x3ab9fd5919374dfbd2bbbf2b2cca1791c6ed6ba29ae93d57f2,-0x5fbcfedbce9dc3013e0fb4c0382a0ca78c95bc7432bf354c2,0x7eb38543bfe366178de58dcbfb95f67a3938176942e2977a,-0x85271d7a8baf94f6ec99c8f1ee5fc01d370aeac65254291,0x6c18c7b1b94f2d72c504b9b3f0922a876adab104f76ffc,-0x417334878200e3d3b4663d066cfdd32ae14920d0655d4,0x1c3c3614afdeea1c89d3b6f40480d6d9969a0bc30fbc,-0x82a21c66325c1cc7180bd859cdfd0eb05d86c803e3,0x1744b853abc9f81fb1278bb915dbe58a1dc69dcc6,-0x24227085ec5c6b87d026bb977f1514999ab508e,0x1941a3d2f31adedd8d785cd78f142e9cb0eae,-0x5aca00861e1b844cbdd91f87f42e335fe5,0x30e61b4ff1c8ebf1b88000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 24 70 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 70 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 54 indices rho q17 m17 17 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 54 indices rho q17 m17 17 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r18 : List ℤ := raw_ints% [-0x1a24c2f8ae395a25c6b0a1a230dc223f9417c800000,-0x25161662e31c769dc38a7618db303290a607d680000,-0x18fb6627c93476e708a348593b8f6e50e39e0a80000,-0xaa283441abc7a31d7b7fccb06e89f3d012c6c96000,-0x336427cf2deae473fb5e1259aaac3033af3fec6800,-0xbb8109dec89379d72789f72840d16be9811455a00,-0x218aad08daf75541899ce38a34c9cb5b0ed847380,-0x4d3d028dc9eb6972cefd706cf5c308c1ba8d2580,-0x919abd650b6b2382c17a9f07c40c08b6da947a0,-0xe36db2cc06a6e7addfcf2eb1bf3df0d2e141e0,-0x128c2179d539492a7d6c74501a9bde7e713a18,-0x145287bcaeb6b69ab95854067ae82c485ce88,-0x12bf4849eb89b253c7a15aad68e6e4632d86,-0xe90685712d2c353c884fe7f903bbcbe498,-0x9822e67e7b96a801eb635a46967b76331,-0x53166059ecca76928e75a3e3f74dc4f8,-0x25ab837e74d497a10c9959482bf9d70,-0xe042d9e0213dab7aaea9623b4e190,-0x43581f2bc8d927f3e3bdb90f1106,-0xfeca6a3ffe8fdfb2f217fd6db8,-0x2db1eeb46114318c50aa4ab52,-0x5d860a7317207558c9856b8,-0x79b88d7f3b7a16f6b9849,-0x4bc6b706f67b89da088]
def m18 : List ℤ := raw_ints% [0x0,-0xc6aea072845b2ea086e62a0ecddb7ee8ed4369f220b5654900,0x16536d5b2049129814800d6464d41e6ab453b8310bffe55af3c0,-0x1370a4449482ce27becd7566b462bc647e558008cd3ac6fb86380,0xaeb9985990defabd65c300f66f6f6d8caa806a07c2d4f342b2670,-0x472a52df5744dd6b068d16bb3091b9bcd0a0058660a06a32e53920,0x1664ddc71c0d50be7292537d3cbb0f5280482f1ec4e8bcc3116eb40,-0x5aa37b707c7938caf1dcbc3cd4678518b1a81208e7b137d4ea10660,0x12efb5cd47e65e4ae86847c78f7bf35ab2ee3e16b5cd73819b173c8c,-0x354d07b6e1dc37e7f132a938ed74e4aaf061b08e11680988a3926ea8,0x802a284dd5d542efc1b22cf3175d0d99abdbe373a0bd776b10684970,-0x10a2e447eccaf78c14b951a8bdd81ae2ddcc9838d2aa75f89237f7df8,0x1e1938533dedc715bce0aba81593a8a32c84fd6e261dc07911cb0874c,-0x2fc1154923e721328ec4a6918b36d44bc3ce1a4d8c18eccca070c1b90,0x42cacc2b95c0c04271d0f099f9c86e8f5dc44a5b4d102e15b7cd9bac0,-0x52b06b05f71e74641491ad75afcab1570921de9a93968a583402638f0,0x5ae42f5e5e3858105c653a5e86e43251f6f9d45123c26f249fc100c83,-0x58e7f87f1d23d973e43321c973a4d4ee2df6f22c1a696bb54dc25b052,0x4d81fb74571479772406a0ca38aab6fc43d2d3798e62d88f9bb7c803c,-0x3c46c1cb18d0de57a7445b16f94d9b06b6efd968baf45c7995612ef96,0x29d3c0c524973223b30b5b2dfc966ed1b6b5bc76eff3e573df5e9aa87,-0x19e40b492bb206efdca2c6a18f163491ce48787c5ef396f8db7063a84,0xe48817fc9f0917d68f7613d6ec678f86c42f0ab3d7ecc9606d660b50,-0x7032d1d33bc014bba8d72d4bf9d697158ad3867ea96bfbd9b14f605c,0x30ebb3651964648f534905a262b2f847c2176e2d420005b906282f07,-0x12e47da64105c93e9a186e68c6cc11a201430b21905df55bfb8bffbe,0x670b73306116c5b49e1fa3295e7cb063d0d8065816ae8e1e692204c,-0x1ee0c7bf9dd29b619cc8711e8dfb4853689e54d31dff038124bf78a,0x817bd4b0c3e9e2e36006d4619a535840cf2e5a2f5dcd13ea09387b,-0x1d80a3a04671c24f5edde62e947cd5894fe2af09116b7b5ecc1608,0x5cd4744db6882f497014f3239cfc4763a7d7b703e51bdaadb3640,-0xf9f1bd40a3d839bc215d32dc47df54764c1df490724e9a441d78,0x239f87cdf48bbefd03c3ff558a2e70f29e984a31fab3f442c349,-0x43f48b64f92e53d123b062db3f28ffdeabc19399898f915face,0x6ad4c227a1b2cc245aff7cefd5e51976238613f69c739a9114,-0x87e73cba53d090dba643d1a7ea34255e227950a73e99acf2a,0x88c92c9ea42ad4a2758afa493f101c5c113d44096f4900a5,-0x69e6ac9a574852e1359dbefa015cedb0c1604f30b7e8084,0x3cd92b0e8fd1672314db75a0f9eb57d7c15f1f7ea3d670,-0x18c46225c870e95298b095f25d62a9de9d8dcf930311c,0x6b62f96ab918b479b578ee3cadc6f65356bc1ca2d61,-0x11c8c4076c6d07738cc0949de83ee4b081e39c17ba,0x1970df55b5d817800c4892a35d5fdefb195dd334,-0x10341b6f32d18eee54dd329b39073273a5d9fe,0x34672d1307be56c819950f1543537ec05dd,-0x18ff7af7312e6897fec0000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 24 72 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 72 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 54 indices rho q18 m18 18 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 54 indices rho q18 m18 18 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r19 : List ℤ := raw_ints% [0x6186e67b663352e10c705d6dba361169b9f882000000,0x8a41ed09b0babf57ef2c3999eb135971d08ca2200000,0x5d11309469d51914c9c7f9229f4471dec1af8cf80000,0x27969a73d8efc55ef4dcd216a58aa033ab4873198000,0xbf2586a8ab20841d207571bb95791976254339e4000,0x2b8c8f6e011c0f2da20d600f56330f9af210e744000,0x7c85faca27a550a9f497519507304335a2845e4400,0x11e71a8295187f127f0325898548ac51e47e9b4280,0x21b5d502f2f26f74f66b72396a4d1e8a401e60e00,0x3496976d99e29b01d67a74dd4cfce107a57991e0,0x44868bb442a78acc7b2ad0f524aa664a6276bc0,0x4af8a549a01a0c10da0af08a22408b52132d08,0x450bffdb5730b617f40029dd1d7a9658e8b80,0x358b28e13e5cca098879c873fd3e53402fba,0x22e3427f7e9ec04ac10276c84e8493d55d8,0x1302f7cedf700f8bddb8110a3fe8b0392f,0x8992ebfa4f5bd00a4016040957687280,0x330c9ca36a761144d6cf04fed305190,0xf486fd0b3fa99011f0d89c1f846b0,0x399f6a5e004329b0cb6f73c668da,0xa4b416e864dd20be91fcb485c0,0x14f9900b86aa1ce35ead85aee,0x1b28c1cf19b12ea4db001f8,0x10ceb9197f1fc10bde057]
def m19 : List ℤ := raw_ints% [0x0,0x180f256dde070aa57055df17caed945e34bb29d451f5f743d700,-0x2aea826cf834eed088a779fd692d8f6896bf80fffba444a038440,0x2510cd00e59f192de7aafc953f126e9e4e7fac65c86af15c696280,-0x14a5b4a9a78b256a591f8bd8835293bb8a15cd2f555f84b7989b610,0x8564953cf9573c16b82749afe60595c7a42738fc4491d8ad1ba75e0,-0x2999fde0d146144933a5a98afe861d29d800aa0ab2b93647b7946be0,0xa6d474ed6f31a5d8d5b3cb19621cc85f399f92420edde38efb127360,-0x2285c858cdca5a6d646cdbd0f698e36f33af0a0039348a7ef8ce81894,0x6036fce38982173bac297a73eeeb7848c7d54a8e2e78d2ca7e7c4f458,-0xe4fe3b819c8d06789221b89aa5825604c352f57d78188662da319dff8,0x1d68f145a41f0f1e6ec0dfd00cb132c46e23126d2e2741edb86bdb2ff8,-0x34a000990f3d31dcfb89587fe1bbafa203e6c6361716d1c7b80395087c,0x528b2f5f3599646e407c7863d4f931f9cf2934c9fff92d277d176041b0,-0x72158eaf74d2dc3488473251bd4282e9bca1925eec50ac4b0e1821bd10,0x8b7f4f974495447c2b32f50a6fbc4775139d7ffe414c7cf30cb803cbb0,-0x975e0aeb48f227252a587f11f3aa2d73afad0cc05c10f004a3b0b1baed,0x92149c884030cfd62047f87e4b81dc195beb15b122e6275e4e480f74ae,-0x7d92c13637bc53ccb97828236a94f74e83c42a753bb5e2d28a2bbce386,0x603af20b189e6f51b85218a7a8e2d462e74765eab7fdc8d20ada027016,-0x41c17898f742a06dbe109cfdd464eacdb11cc3a6f8ea616555ccce6f53,0x280ce039ce96aaab7bd75b03d84b20892cfd95b9906f48d8b886f5310c,-0x15b910c0cac810d567ded1897fb773f499b8e452f8087da6937cf32c84,0xa79eb5a53994382157187f755fa70a5405bd9b092181e0296930725cc,-0x47b91a4b228c02e1452923bab9f255be4971aeb45073d527d2ee3bb3d,0x1b27485d160440a3a8e6890bc72611913cb3c5b6d13b1fb973e5ce972,-0x9104df5944cafd20f004d8cc53a82d3fc62bf8a7ddfecf7f5d6e4432,0x2a7f3d9dffc11397dc77299e831695bf8f03472ae4224dc15379889a,-0xae07376e4f5bc5c49228c5ae4f4304f5387efe161386f43fcb7684b,0x26a94fe48912214b8df6b09ed258405f44da45b701a4a847637bdd8,-0x7667032366601b28ae6911062e944c2cad78a89966969d9c787a28,0x135af13c2d90dd6ff24bc36247f181873739a6a9b3ed076cdf6498,-0x2ac7faff001a9e8b9488934bad85e163b64f75a2ab53bc79b52df,0x4ee7ad7a0cbb9e0707dd2ad1318e00fee708ce26871cae161b92,-0x7798017a22b833397de2cb5bc82e53a18af25f52b227739ac2a,0x9234822821432a4b6c73b7a57d383870854f486d4689dcb6ca,-0x8ce3ae6fe26f4c5454873ab6b6620caad88ceec4b258128c1,0x67fc67600e136ad164faa2cbdfd8e8a23c103b52fe61decc,-0x38ace4cfb2ff9b11b484d3f5207b0abafae81007f282c24,0x15c171a2c88b2de2603e6bc80973cffb0d5e22b6805bcc,-0x585c2bfd467635748837aef1f144ef208cb87c351e63,0xd996deb84387efe59f58389600a42a0ce4505f15b6,-0x11e9f11c3245c724cd98fe01ef8c3116f7233cc26,0xa64d13de0aefc677cc2b49d92139ae1851b8ce,-0x1e3cf2bf6e12bcf6a7fe29a25361658c4115,0xcc6bb0f63c9d59a79200000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 24 74 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 74 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 54 indices rho q19 m19 19 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 54 indices rho q19 m19 19 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r20 : List ℤ := raw_ints% [-0x15a1c5974afad45aa698eb807baa6d72009e7ce9c00000,-0x1ea5c96c6a576f570d2a6770b568ae5dd62c8b964c0000,-0x149de4681553c39f3f24ffeb17b6ddddb9a0a9c5740000,-0x8c37dee30b6395de24bccaca73315fe77da5db16b5000,-0x2a482196cb82a660d9afcbf1b8e7de61cc159cf5aac00,-0x9a0091f627d520c3478e75017c4823fd61f91641b300,-0x1b7f52d8254335cc8322a3a6dcc03ae9ab23cb9ef240,-0x3f310a70c590f69ed9c3f47ecf9bd6448b22fb32340,-0x76dcd0945f517040ca649587a8ecc21cf565ba5c90,-0xb936e5aa3b758f83c079afbc0e2f123b2a3532a50,-0xf10b818c4882f5a5aa1ebbe9c65d4c536c5cc78c,-0x1075c387ea5a7c25cbb80e53d8c9e6fbabba69fc,-0xf23057a0c0b975952fb36187f776c27fc5cf9f,-0xbb8101a70dc6fff9b1b4b5bef9a92be7b6118,-0x79f463292e47c663c9d4a61e96afd371ada8,-0x425396d17ea4e6ae55e17ce74de1578e97c,-0x1dee9d62ece07a3c387b1da596513de37a,-0xb14784dfd253ef3e5ce00d35187b02a0,-0x34ee1d897877e6d78dc08bd974940a8,-0xc6f6e71eea9f3900d69f6cbb7c474,-0x236c4934561e9621ff99773a084f,-0x47e646e68760dd1b2165bdf6b8,-0x5cb0b339a91bf99bdbcf73ec,-0x391289382b4de44d6e1d14]
def m20 : List ℤ := raw_ints% [0x0,-0x2e9d5884de2da4a089a6603e192c4f76862aa10b5ecc8f1370900,0x5282fdfa670058ee8e85506f6ab31c3f1ba1f8adc1caa66e6d03c0,-0x46b308cef5873c6d38920650ee15075a18f03316939f298cb2dab80,0x270fa3386c7a70f41121f339f1e374caca43a3aa588ce9af72beb070,-0xfa3a189a124c6835d4b02ab1ec277c69e910cfa6e168b57d6b89bd20,0x4d5bbbf6c65efe73cebeeb105ea907505ffa20675dbb5b07aa17788c0,-0x1336c8789b55a1f2b50f3cccf16130dd951850b381d2f3432f85f27b60,0x3f05bd11db6972690df0a20c28c300bf2b133af4479112dcc2a338138c,-0xadf2444a66308bfe331f8d65935a4f85d44a604c9b82d379ce8df773a8,0x199d90b9f6a18b3eb180cc964ccb6fa3281fce3985c1a77f64e1b633ed0,-0x34171b0b3a45981a7a8aa377f9652c39aa5ffd664a5a0dfff6a01bb0738,0x5c33cbc7c57362c950a60c42b936d71937c85f3cdbcd7900359f5dc144c,-0x8effdce2d7afe11e342e25f59f618c4434c45e13131126fa8d0509a3850,0xc35585b4e8b114cb254d50eb3f68685fca3bfa718bb496a8657d263a340,-0xebf17dbc13fcb11ba84d824047f8ff6909fbbd7cfa865912790c1f86730,0xfcc6aa7b712f606dfc1434a1e34e5c3f27fa3cc5afcaaa968a9d76a3a03,-0xf0b886f2e75e97ba09efe5cbd09c54b20300bc70359cca1b788fe6a9312,0xcc1143aaf0c81846c84b588e40bab42fbcb6fbfaf43f94742d3f2b813f4,-0x9a1eddac500ec017d811b7fd42880cceea5983fdeb3902b473bbf499ea6,0x67b78a6602b0fe5f0d9c906575397205f5a751c6be00cd610eb13848647,-0x3e2ab1dc2074c801ec53633c427b2d9166be2fb87d9c30c566e5d2923f4,0x2127ab91ab2c6280ffe6a931bf63ae81c7cbbaf8ee762a5af0b0ebdff30,-0xfb5465968c40ac1b54ab43a63c3a71891ef7a678050c80be39d69cc82c,0x698b90c22059f9db0a1ce3590744d56db0fe33c94dac5c03e51dca9a17,-0x272c96686c67e7b0e483b0c16add86b442b0a23754f606fc5d6b42c54e,0xccdf431c733d2d5b93ef8f8d592e20521829f70a41ee3f3cb3f24cee4,-0x3ab68da74e1c612403f0721c37324fb2287b47ce00183339f84f74f0a,0xeacbb06f87ed4c08b437f0a3586542433f95ebc34e3f55e1a601546b,-0x32db52300f421ef25824ad3f4ef5ded2ed4222e41bfaeac100d1b928,0x9795fe4d6ead7dcf9954fadb7a5d95078d3267181759807943dbb40,-0x1811aa7d8fe4d43b7a7fc590242d0ecc1e12bd2e86499465a0a1058,0x338eef89f0d9b09db18f631ba01e0128340039ff1b93be688bfe69,-0x5beceaf760e1aa8b8c754aea820ba4f97ce49e4cf097c9ba018ae,0x864c9b2e41fbac12a5ccdcfa818d4c34f6b1644a7c1c685aecfc,-0x9dbc94e4b2148a1904b40b1bb42935ea1c078a41049fd6dc73a,0x917bd9ee5b8bd05f74a295773c529befceb0936c873f34ab45,-0x6653a3f9f28e5c9a266bd41e59a34dcd264a1c5647b774034,0x34e19eb38677af9486012c59f87fa78345592adb7de2db90,-0x1322adec00ab6b6a049369fab0ff08fb5b722d075bb1e2c,0x48c4740d67585f5f44ea22173f83062c90f5286446fb1,-0xa675a9d26d2975b294346a70709c48484d530e65f8a,0xc9d5aa6578a924d39bea7d979abef9106e69e2b9c,-0x6aa7bb9bd1c9d24ae7740dfbf87ed6671235f1e,0x11717b6ed2b7af2e508efd9260319310d5f8d,-0x6873fc7af050f73edb000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 24 76 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 76 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 54 indices rho q20 m20 20 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 54 indices rho q20 m20 20 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r21 : List ℤ := raw_ints% [0x497453ef9d08683c939ef5f3c289f850037962d35000000,0x680297ae1f3d99a53a6f8850462c40632de4f12add00000,0x45ecfaf241ebf5941487bf95de5b25d767acbf0f0a40000,0x1db443fa23faf745859fce1903bd2c1a871174bf0e3c000,0x8f364d6d270b40fc1e00dacc95fc818b9e46a9fc9ac000,0x20938ed3ae955b2f7ac2d898d1c879516d6bd512e1b800,0x5cfd125deda8b9b96ba1d432c29fc3258916115f66800,0xd581a0253fc8bc06c06df9b2efe9e98684e96d1ea4c0,0x19137228b64739b95b033f8c894ceae6b18cc93a4180,0x2708765fc47fcccedc46303e9b81d8b738741b8f730,0x32bdc59415b5009e92606c390e9020048289985ac0,0x375ec340302f598f1daaf5c783941d85fe1d94144,0x32d9aa528dc629ae5293e0bbac8046782a19b6d8,0x274f7b2ea8730b996edd72af280d566a3722f81,0x1986d2947a4e56d8503fe073fdaff6d426bd80,0xddbbc0ebeb023c270e626148ab69c04d3648,0x63de7900c033edcdc6ebaec659dcc7bd570,0x24e37bd15037ae7cba9f6c3eb7f4f87a06,0xafcc5400fb65f3fc39fafff5a71d2000,0x2930f5de7c60aaf1dc78aa52ed46108,0x74fc6f9d7560006a888e704cc7078,0xeca71cb67b2d1f57889ad22d551,0x12fec46f5366c23c47b6c58180,0xba52fa1060e6bc1b17db4a4]
def m21 : List ℤ := raw_ints% [0x0,0x5a50db816e786ef70ab25a7850c5d9f5a3f2980607ac5535aa1700,-0x9eab7a7acb01077beeebd97e2eb358b6a5b5d17482a9d936f337440,0x86e77fd1c0921e1bd87344b41cbd94d2f902c9f3dab3ef800a9f4a80,-0x49f06e522d354fff20a56df5a85d861087700e40aabb4ae3202170010,0x1d5c00c67e9f31fd6701e75951dace1e74632b9f14ff9e36fe0c6ec9e0,-0x8ffc4569959236598808dd3cdd1aec5f8a0c0f0f2e2cd2848e73c58f60,0x23725f2ac262206df4a6e4e3251466a9c35e97d1a16eaa08cf9131d8c60,-0x7333e4cc815ce601cdecdfe176dd740596cec3c4b4e6b8a2b1da4e2e694,0x13af3c8213de8ace49704ec161c004fcf08a2cb0c5c9242849725e801f58,-0x2dec7ea3c2007e34601c7032685d7183efd42e09167fc17be41ea80120d8,0x5c6f1b7ea9348774c6c68369e4efc112275a935990fb562b53eb9eca4038,-0xa1e01c10189c0cac654d6f7f9357306b53705ec977eb6a250c4c11ba95bc,0xf848c5cd01234d7363eaa6984e3a53368baa6caffe9e5a33bd53d5ce1cf0,-0x14f3fd0a01b30239fbb0243b34cea4ccc120d3544f3d40c5d8e4a75652e50,0x1901719c79eb9c39797fa691253a341ecf71e059923cb9035ee29bf036bf0,-0x1a744e54df30476db52d559ce2bd513eae0022a53fd1d47ab4b6595f0f2ad,0x18dcfdd48089dc1d7bbac093c9cb44d4802129fa3dd78b189693a1a1316ee,-0x14ca03083ffa390cc00fe3d87450f94080b21df2e7f47f73c97f8bc7c571e,0xf79d0f3ff79ecdcd13c554aeb801712e9bb9425fa99782668e59b2945ce6,-0xa4210fabb7c759823dc393e5e3169f179787c46051800b831443416452e3,0x60d2da0fc9a61669fcc94a8157ea85d70635b12493906c91467626f7709c,-0x32c7be4cec44c61d1fbb7043723b0897822392cba324fc0c167a6fa5d2d4,0x17a3235526933ce0a6b86de446c12f9d920abf4c2c9c6105a865f718b11c,-0x9be2b8ee15621cb49a9a04349e03bf2860c9b69832f8ba3bd79674dc1bd,0x38ba0d9b256e22243b766f3080c6570fdc8f2d1f48e47a1a9d203130322,-0x1228442a77c80129232ba7f373b2b901bf627721544feb69f93f12e3cba,0x516c619a9240b9b11f161778c24ddc0b825f34035180beb7b8a067769a,-0x13df9f252b406b7a8033487793f839f379da6abaf19439eb9c98187e1b,0x432618d79f022957aa71706d592862abb1a439cef1019bdfc616623b8,-0xc2c8053a91d2f7caa2dce0751e942b43c74154a90da78fff942b9048,0x1e099b28264f32d348d1862d2d224e72b8f57a71162d6555486cf578,-0x3e5969ca526a202953b0f2ea86277361eb98959052cc8068e6ea21f,0x6b71372f2cbd554026bcfb229ac348ec3b0146618b9b812abdce32,-0x9744c470957419785055e91e4c9910d1dd49cb3dbdd0e95d4acd2,0xaaa5407432eb1125fbcd827cd4118729e92f71ac2ef75186329a,-0x9697c6226ee95a3e8392aa4e60a4a3a910a7e329e7daf4325f1,0x64e6d1cd1bca1c34719f567ecbc282e01ee939732f565a9b1c,-0x316c4c6886261b00659e499ba8cd77e1ad9d5e605549971f4,0x10d9fb11f49c2266b8e3076dbbc7bce024eec3466d450f5c,-0x3bf942c454e1daf50128aaf3f52020be07cee06f7a36e3,0x7f64a264a76fd58f3e6d45d5275bc3e3db90e4372b26,-0x8e22894892821aae43275fc2de6fdc42a517b6977e,0x44639bfae0c5eeab4f23d509255ea557a9ee60ee,-0xa0f41baa19f6d4d0c12c3f4a5f9c10763ff45,0x355c2bee1d6040d0988000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 24 78 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 78 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 54 indices rho q21 m21 21 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 54 indices rho q21 m21 21 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r22 : List ℤ := raw_ints% [-0xefce7005e4290c0071e345ca994d2ef6ddf92d61d9000000,-0x1536270921ac132e5481b19810ff1c5b8e27d15a1a1d00000,-0xe40a0061dca0190945ebb8081e45896c8162d7dd3be00000,-0x60cfbbcaf3f157c4b9aa119552684d96a021e0a25deec000,-0x1d2735fe000806f18b4ecb483d76e6acac17674865439000,-0x6a075518347e8aa746866952ca22b7e7dec7e7560737400,-0x12e6d1ff5026db92c48102295c4fe17ce486f39e9d3ff00,-0x2b5d0c9f2e2f5421b8fe2da27be25b87aaed1873487b00,-0x516a4467c081c48d6af97d1456ad442423946a4bc7f00,-0x7e9bb90e96573f5649d75b62f5941d45608d2aeafd40,-0xa469ea49a97db64cf285198443c5039f8c2c95e1b20,-0xb3358eb3689cb11e3fdf5631ce4d4339c037c2e650,-0xa460a2fa06552d1b3b0d75c6e67ec95a01bea2220,-0x7ee75365705f146ebd96e903681f9c22ac1506c8,-0x52490884b294c1a7eb51f6528fc0ab4f1538ef7,-0x2c99c6c12806b7718a7840768ca553d10b4d30,-0x140d841efa65d2f801789114d0234eb572114,-0x7647c28ecf2ed541a5a030bb6b6c84f9610,-0x2327937cb4bc8e087b200bb44dac0ded1a,-0x837accb8a48bbbc98f856fd80162db70,-0x1746c3f527c914583c209074eeba454,-0x2ef25e04e1f61c3e42aa82108cda8,-0x3c1745d7568699c14595c6c5347,-0x24b36a30bab9ac1d0c308ba50]
def m22 : List ℤ := raw_ints% [0x0,-0xaefca94ac60956fea4b98f491c7f564beda6068baedde517f98c900,0x1312de44c7bc4a975dd22defc506d159b1562c524f8255b84573b13c0,-0x1018360f4ec8cd37400a6153e18fe6e3cf162aee2579a419df57f43380,0x8c0a0e01fb53eddfe617b61165e5c6f7ac7770832c6f76403831be6a70,-0x37285d3741ae7d61f4ee4f83b49dacf2d500996c80c3b02cebf15552120,0x10c3f8bbba5fc15226a525d4ec617561beba6c4c08f7999a360451b97240,-0x41778fa715d1df6f43fd6e2584dad2fd6d613e3d89209b5705dedcb41860,0xd2dc88ad8007eb5a735f917b1cd21279b08fbd4d81e1da4221d05e37128c,-0x23b1c389ae5adc0f82281fbe9a44beff6e24a54fa404cccd1c8a95f43c0a8,0x52785ce3a79b1fcf1831f1e9d3804c20b0e7866db7db1a8618a2ab823ff30,-0xa4539910d6e2aa4c5202918b6673fe0f79665b317640c66991fe943c77a78,0x11cc570860e9a7c2eb25248ab7beacd74e15df120295c4bec52ef1c936174c,-0x1b007be73610e98b07c6dc6bb6a724590402d7129b8f8d0ec50d5c5a344f10,0x240bd6f35cbfdc5552633a22fe6c987194b2b5cd4de96233f85cd9c456afc0,-0x2a824caa1d438ab671991c7e9e7ae3e0b7e249470fd04953de02037c93b370,0x2c6a71e75842a8f6f90fc3093aeaecf5ae7060f6f50188618ac6eb41198583,-0x29346a54d17e2b49f8407dc323e332c7cc8d073343897b1a704e2fe51e2bd2,0x21fc840456948199fd9779aa8010a52cdb999361179665f29447fffd90456c,-0x18f0e385041a784a8585936e23fe96b315a56b3ef4af3156eec3d7efc52636,0x10491695ba2b2b895e29127f72be735e86d850f29d403bf8fdf8fc4647b987,-0x974e18585aef317e9ffb866971963a291bb413cbdea24a802b08a78e669e4,0x4e0b06e675a071ec05d4498093add437c29e474c093270a07265d3997da10,-0x23b1ce80e45656e72a0fc77f162f132865c214c710f71c64dde84ac3eed7c,0xe7110622e701e096183efdc50a27209046386e1d282f3e3f575f6486dea7,-0x5271e11634846d9833a063097cc3f15c831f3e0e21d63a0ea26fad220e5e,0x19d7ca534dc3078c7ab9947a4d1457827d3253903a182c25a9133a21423c,-0x7156404328c2f3daf311e0e68fd6272bc371af09ba962f04fdb57f34b8a,0x1b037cb1135a726a0de6809973b947f193b7434092b4ab0d1d1c2a7425b,-0x58fc076f76ae49848eca17c5d59100f71538f982894ff071322d356348,0xfb2ef49fc3c463e231d9b5c84592fad0eac8fc451b79110c34f555840,-0x259dd8cf74864b8a0788042930603238488309ee5a21752a3ff0b8c38,0x4ba67c41123b23d48e82d6d4f73ade042931db5b2d2d588eeb49da89,-0x7df95cc3f1a4de53e511bc703e499f47310c48adf7ab3c844e0e38e,0xaae150004998db2f554b8fce5513c84c65cdafb4cbe16d61670824,-0xb91978eec3aaf46eb3e319dad25738f3ffca511c265feef54c1ca,0x9c3e6f3585866eac6be9b4da8892065dc172b62e2a22342af965,-0x63b108fff4fb31837dd2dc5c8fe485b8685b70571ea70cefa64,0x2e4356e6b1d2e2bf404e4c32c3b38883b5a9346fbcca1c51b0,-0xedb674134f0ec837b3c9fb4bbf1bda91e09608c182ab86bc,0x317703c22c2a7c06d8412ec296e02d13a74ab1d8e70a981,-0x61870a396141d747bc7f1bf166c65079d80ee51a740da,0x641849a949e20f6a6fadcd2800127335032318eb744,-0x2bd7f5be766597befe28ef0102eeb8f7074e0323e,0x5ccbf23417687de09142e5f1abd6cc643f8e3d,-0x1b40baa7bf6752feb2c0000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 24 80 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 80 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 54 indices rho q22 m22 22 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 54 indices rho q22 m22 22 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r23 : List ℤ := raw_ints% [0x2f3c439def67b53afb633f8d1232309889b6010f8e54000000,0x42d1315b3493576542833207483d449d734a0a8c00fd400000,0x2cdf4e4ede96e003ff9b5624ed356fc5b4191bd866c1f00000,0x130a10b0ff7b0316517176ddff9223a80c57a514b8489f0000,0x5badadfc040b5650ccd9289e803e077968ce7ce38d1618000,0x14d365f5de6291c0433cd55130d0698111ba7c909eb8c0000,0x3b5c169c56d445ffd9b40178a11ec06a20940ab0c62b7800,0x8813dda3b1e7b0015a147678bab6c7288078fd44992dd00,0xff46e2551cc65fa40c40b23623fc3974fa68493365b800,0x18ca0db6d31e923be712c17e8932de95c74378c4adf000,0x2029181809b7c28f232ae3c53e7582d3bf7296256cf00,0x2304a8f4645684c3c0aa7126117d506045804bd2e020,0x201573d322f330f3d79828753a097040b51ffe30300,0x18bd3807f77dbeccc49d3fc289e6d6d4920816ca60,0x10050593f09a9f122cce7192c81f0e74768a18798,0x8ab9d42604e71e2a626ec0e57e86a1c1fa3c8c9,0x3e45c9b277ceff382f42c961d1f28776f96880,0x16eab0591a432c0c49c5bda7945ebae7994ec,0x6cc4d2c4e0f18640922cffe75c1151e2470,0x195ef172ecd9db1428ecec46e1833481a6,0x47b1d694196143185c320d27c1bcb240,0x90390bf059d93f5dacd2115783822c,0xb80f75c158bd464485d56760d738,0x700b849bed4d4e3d4b2f8846f9]
def m23 : List ℤ := raw_ints% [0x0,0x153098800dfb2188d5f27859da736b7331c71acaea2cdebde73805700,-0x24b140371826408e1212026058cf85a17bb8a0cb3af6165ceed0276440,0x1ebbce9a900c0373d9a3b70fd0339a29324ef46eec1bf8302a217d97280,-0x10960e38db4719f8b8667836d4a18143de343d81eda3d18b284401dbba10,0x67b39b4584ccbc8a2fb755330b13b88f953575a0d4c8c2370b7311aefde0,-0x1f4369cfbfcf54345ad28838df36af0d96a5f7bd7bce613f2bd40fddd2ee0,0x790b9a017581a321b11371db8f0531216dc7965cd8e4da8dfc9294fae6d60,-0x182725701d4577e1f41b31115b6e7316e0f0a75adebc7bc05667d2b271d494,0x40d1fd03227e2cfe95d5f0374990b38a7997b3dff30f8bd0d143cca0d3c258,-0x9457ee72c454b6595b523c1a4a01ceb6828567a34774e05a1c24c84db2e8b8,0x124aa7a7e3066d11f1b0d149d3c442b54048842c781597f1037ac07a915b278,-0x1f5f75540d0aed1ae02f9bac688888202ab011f44d22f8253bf1d56cbb766fc,0x2f161ceb3cda633f6e167dae54f3ed953b4fa8523911d31afe64faa93d62e30,-0x3e27d0af217929876a041b8995adb73b8b96b2969f2815c92d2472d2d7a2d90,0x48719178297641afddbe5ff32fd41ba3d64c8c30c522fd85eedfea712af8a30,-0x4ac4e1e48431f4737c6f860f65346ab7f24f50729b612501a353d7e88b6c26d,0x447a1929a27508b57148ff28feae800ff8356c2a8fe441576d87e19f8880b2e,-0x37b95d420dee30cb378936dabf7cacc2775c54eafda4a83103f0cebbb530776,0x285165500e32a58c5438de4be717e5996e474c0ae16e1d8edd88b98f4f13036,-0x19efd00c3d3efc186436cd19566792f29ca4a5232a58675be9f0a19330df373,0xed389db00a0f028df5a3fde28af3f51e6b1ec496a3a4f0bcc604329fc8f7ac,-0x7859879024778d6978f8f444544322a00e9cfa990ec3ef1ce6301cdd2418a4,0x3616fc8cfe0c92e2d341654fbe8567359043f7f43260486e832e7e03cbc9ec,-0x157b8b2596a36ef51be84a8a37fd1bf14a638743bde4001aa5f8ba1b09123d,0x7841152f6126a7fd7090106eac4791317c3aed688f462b135407c7bdb1b52,-0x24ea597d0323e00b1a6f4757c0131473b6d1903ff0019e9575523835d8c82,0x9e556c5d5097ccffb52fe4382df57f94ae277f7817ce9948a2cf86e5a59a,-0x24da2a461f50a08e1b501de9da0baa5f0ccc0ef304be20aeb14eb4e4faeb,0x7657e60f67c3c2c8ccd9901b4f80b4f52b2526aa945ae5f3a7a277fc298,-0x1450dd0843e4aa5c53ce080e3179f4a36072d32bcb51e621903165c8d68,0x2f449f18fdf6b713ad4e77dfae8c51aa5a8edc41fc44cad72111ad6758,-0x5c164e90e92baa67e6ec10625f5395fd64c2be6f1a41c99c22c87f55f,0x94277460044c2d1b569c880b60b9e72001b9939c9891a81cd17e97d2,-0xc194648a60bbe8b4674505708958933cfc53e93c13cb9bf7e2328ba,0xc94a0dffea1696ad6fc84a3277f30ba9dc13bec4dcc149d130eeea,-0xa277bdb939bd29f93c020a6fc368abd29162434b3552f57b0be21,0x62adf3ceba2d011add1c358062cfe007a19938508c1cedd498ec,-0x2b5e65a27deb481b8a4d0e4aed7a6c5eb89c39da804caf7af44,0xd1cce95c6f6f47521bc087e1c7a678fa15f8023be6c5fe66c,-0x28d2ffd5d6119bd2aa3b8c576d4e2233e5bbf0df5431c963,0x4aaf52a034fd65c0ab3e9d8bc65f118004ad9fcf708916,-0x467d0ddcf77e7a2f4d43ba4049baf076045d6f824496,0x1c1a1bc9a48bdd712cd2d2fac2da2384f6df89270e,-0x357c964207be4e3379e46d980d268113dddca75,0xdea7698671ceac975200000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 24 82 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 82 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 54 indices rho q23 m23 23 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 54 indices rho q23 m23 23 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r24 : List ℤ := raw_ints% [-0x9034cd85e29a6f18ceec5884ba84299c427df1085c8aa400000,-0xcbe5412083c56fe24bc6b5953b34aa7d3d026644a156df40000,-0x88dcf378d433f5384cd7e6c8f3c04f6cab30717e8d09aec0000,-0x3a0a6587a9849aa2b40ae9416274f6adf32979a9fef099bb000,-0x1175217d334ff44ee6e6dc60d4c27ca89a17a8a6a9f61e11400,-0x3f698e628fb122bcc47ae95a216af36f954f19f315a96f1d00,-0xb4a05158b9a751442fdbca0080506759277d50af5a03c79c0,-0x19dc7d7aa9290e4555592a9633044c5df67b34f5258bdbcc0,-0x307a65375e68cad08567e6184c8067ae41941221b92866f0,-0x4b427ae537be024b594d8b070e3cbc8b0176b24fb87eeb0,-0x618d66000f98f218366e3d74bce0b0ef4361a5ccd8e6d4,-0x6a1e738a597f9880dfefac4eaa5abd1c5d13895fc2a84,-0x6120373bf23dff37f883896237a6042b108933ffe989,-0x4aceb96ad3200dd871280486efdf3446fb4b57204e8,-0x3061be150cf9b6ac014a67b04e191146b88dfabc9e,-0x1a26acd35e88d3b9e7fee5963937e9b5fbdf06cd4,-0xbb8cee515493250ee69c3768414253263a4633e,-0x44e909a88d78c47dbbc4e2ca92217dfdc63860,-0x1467f1a6eb66e3b5ba1645c5d11b3baa87b5c,-0x4c02d128131cfe589498ffbc7c75b300b2c,-0xd657b5abc4dd727e8151f00cecee5ade1,-0x1ae2ab2f44072787974195e7ee129fc8,-0x2238ec13d3475cfb6549f41c34d1da,-0x14c598abb5140cc3879d7dc0e7fc]
def m24 : List ℤ := raw_ints% [0x0,-0x290e27781b1690f91e85c92e173fa02f3071c3e925b6ef8feffc8a8900,0x4699395c2e77cf23c20f1e2e48d468efd174d803cbf2b9dae22b4c523c0,-0x3ab58901fe5e298e299cd54d9f25f894ccfb18232f728f6fdea72865fb80,0x1f72c76117e51f8bec084f22eef193b51a098f0851b09d5f4d7e45fcfd470,-0xc31c33871e3d3db98008c6040fce5ecc87775d7c42ee22bf78ab67c626520,0x3a59d0064efad4955b8d6fca6972a64ef440212e64591b2d0c8b5b515707c0,-0xe00cc2759d7b9ad9aa217761533eee56425cb868bdfe9c22c83784ace71d60,0x2c5234697428237bec5ffdcd8810f3e617839dc8f4e5020b98f291783a0b98c,-0x75e1c5d0ca47a3e3897790508cd4c296068226b0ba87ef164c8b2232db515a8,0x10b43c1855bd97419e8b4b85ddb1c73f5179d9fd616066d56354d1c4b650e290,-0x20a2bda55f947dfa5e913a3baf080b4ee3d1f6747751acac967b6a87ba94a7b8,0x3768c9239f73b161aef799b0c2cd3158fe10886429728976f0d51d86f9cf904c,-0x5248dd2470f3f8fab7e5827363e064a2434055e0dc2aef9922535d5869868fd0,0x6b6bf735ddfc9f8174a20c47e4146c55fdcfe01020e075932d18ee6a7b3cd040,-0x7bc298ee90efabe65fa25a9dd6b7ebccc665703c071e53843e44ddb6aa328db0,0x7e314aa759b85aac601106c5c088ce7520b5899109e98f0f87705d9e7dd3af03,-0x721cb88524a295c966fdac452d71bacba7b86c5ffe11f16f07da8806974e8a92,0x5ba0f1850b3ed3fae6667a268a540cbbda91bbb405ece64616e36dbb15cba2a4,-0x415f318a11a426c613df7083dae5a9020d2176830d7ebc107533cb8d0dffaa46,0x296feb136ba4f58eaa8f576138d9dc18b0ca85b65f2bd60825038b31d7bcc447,-0x1752161c53730631fbebbb5c86762371e5963946c11435df65c6c88dbb026854,0xba3604614ff8e60e7450f7f6cceb1c9541d64401cd7e1086f30306222ac37f0,-0x523ef3595e87f7a5074889a6ccdf4bdd6e565e453a1a865d9b7518ff569dc4c,0x2011654779d984d9f5df8489884ab079fc8e61727c777e7968dfa969bc0ecb7,-0xb0064f18bd97564d93f4c732ceacb038285573252210981d27b1b8482beeee,0x34eb9cfe13f2222027d8ac8343e457201d490b9d45dd688f1b89f570ad7c54,-0xddfc8d0f9dc04b994cf9cf4cbcb12f47b6b981502ba0b1eacc944227a050a,0x3273f845f633bf81b82b57b80987390214ed3da2b78d7c3200def96b1724b,-0x9df0f04e1c020d72a0aaaadc39c40298a93b9aa665a42b69858071e79c68,0x1a6178f14cc3fb158ccd7a8382acf892f5aa33633ea2b9ef380cc1324540,-0x3b97bd99c48da6994331e3b0aa64a26bb3557f21c3c7056d228d06ad918,0x70731ba316d6467065ddf0c062fc559817a1089df6f464e4da1b0077a9,-0xaec1a7d9d729a992a92593c68707a3d9a3dbfcf2f35b43695fa8dd36e,0xdbe4b87ff83d1998046ccd665955e63ded0dec54d952617a594cf48c,-0xdb6e77a5980318326b42d63e22574c24127d9c210b4a4c91089d2da,0xa94c9005192731d72071ca978ab1c24e7f0bbedd94e33a1101cb05,-0x61d9bb3964b16c52a3ad8103293df70a600b31b20418c903c5b14,0x28b6308ceaa2ebe378d82563eff4226f657a65b2577b9f0354d0,-0xb958f67350f1be2a634f95530d2916047ec264a16cbfba26cc,0x21b680c97a7de78b3c9d92fb9f4f6e31aaf71282811088ad1,-0x3934d0b4dfcfff5d3218312222cde7b5e029d96cd289faa,0x31a336227a1c95205639fa0a398389c5d44235a8e3c2c,-0x12022c24d91f1f1b3381ffe0c1971297ea58bd9735e,0x1ed21668eab262b0de91d9e4dcb84c7c69d241ed,-0x71aab648ec9ea093cb000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 24 84 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 84 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 54 indices rho q24 m24 24 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 54 indices rho q24 m24 24 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r25 : List ℤ := raw_ints% [0x1abbf40929aa497b9f419457eff06185eb8d0df17ace4cf000000,0x25c8adb46ea44adec55b0339a95ad931010bf4c645ad94b700000,0x1959bfb8b824072ab9684fdc2129059c85c02537e10fd4fdc0000,0xabed093817ac712e95147af3106f02ee9a2f3082bb805eff4000,0x33af5bc5f1b249d0246ccf869a70e300a05c00927d7ce6fd8000,0xbba221b51cb5e3f2716cd3b7c6b7a00e138e0362f525a77d800,0x2162359b3f26a26a074d27cd4c7cf6bed59bb17f2ab428f0400,0x4c6cf8eec5f518e7f8cf0edec55aede77381f44286acc05b40,0x8f299bb92eb13b7610ca3439291cb732d9554fb0e84dd0580,0xde15797095add0285fb4afb180781033de050a8241beb850,0x11fa1d07d415b28a3e808acd7dd2a14db7d09c8dc30ab780,0x1389d56c8e184362060dd033109fc9a3e62aa4669eb6e9c,0x11dd956b7ee1311a55097dcc0fa3342415e156fa50ecb8,0xdbefdf9cf8fceda0887b05791dd95aa6f3524ec971d7,0x8e15c77e22933826438a60f526e48325f108bdc8960,0x4cb4a369cbb5b9717feee1024fc13894bea02dc832,0x22563b3bbdb11898e6b05cf7a4d3b9000f3ff7f30,0xc9910562d937a4e808ba3f686e531aa898c9d42,0x3b982fe5a892c090ba5bb3d9fed00f216c1580,0xdd99c39ecacc448a5e2df547b3882153c6b4,0x26fb2ea9bce6e87a23e4ce18b37a045e2d8,0x4e113fb890783b09387139381aa36a0ff,0x6323f0442ee7504585c36fd29e3f160,0x3c04f0613c14a5a0ea1f5c87346d6]
def m25 : List ℤ := raw_ints% [0x0,0x4f8b6c78b47bb8e2ab2335c94d0b465b6ddc6b93b9127026e0f94c69700,-0x87dc3f674b6dcf343634366e7307ec9dab18bf6c2d5b6754e2b4e3df5440,0x703082683543ed962d8d7dead73ab09e6c0c5324c91a96565376ad749da80,-0x3ba8ed567429f9f207fd9d09c3fe68e0077dc54f399fa513bc0172ae176410,0x16f5a6ce213a05ffc2c6ae94dbcd9afe40fb201e5b98b62de3e248d953611e0,-0x6d0137282e9c6125822ca32a5c7736168befb57009a09fdce3179cd31852a60,0x19f26511bb14550d2c10a13e6ffbd82ff0d002dca123052742f3eb94e4d75660,-0x516e6b61935160358e1454c5b9af13935f26b311d661237f39ccaad280cba294,0xd6af083369b972e695279a8f7887db19dd9de6d6bd427a315dcbfe3908221d58,-0x1e24955d64eacd7f3c2de6cd1ec163141742f04055bb0a5ef19faee94b467ef98,0x3a54b20c2213f35a36e75a19d500af82e355f450cdcf1fe298443ea24fec916b8,-0x620cd804b415ebf392148f8dd8543ed7d9a65ac82c75572406f2e6b9cb6a88c3c,0x901876a2cd081315e2e11a81d8c3f956600f453b8a2b637db213955633a524570,-0xba129f0d191e77bde120f804275f61aa95a3a98c930235d6fdc040c92745a5ad0,0xd3efecb1c3345f8d25b49ae6b1f6cfa15e5f8534ffe168a9bda03d5e6382a1670,-0xd5875e8ef543a5b44597148b0c32c4f3997c6fcc11e21ae3e1e22233dd55a9a2d,0xbeacbe3c1ec4a3ea1aa2b337fd4a2318c0800bb493d9780bf3246b4f33fca016e,-0x9718927c551d1d0dddc5b4ef64bec90a758f5f099ab5d0e2c2fd3ddf4ec3cda8e,0x6a4f35a9fbecd8fd4148bdda59e0d2df197b35e9db15fb9d43923807963b2fe06,-0x4267d57eb8421ecbe44fa21c1b27378295ff04af29dedae207c53be3a2b32c503,0x24cc847fc9344907a25af7869f05ba76d444b1a5fb2241c6a4140c195946f2a3c,-0x121105a571773a59653039fb480d5a243528220c3f0ad23e70d4c64add1cd15f4,0x7d7b0828ef37032363589a2dbeb8ce77121169058e1cc3e65e4cfd55b0631c3c,-0x3008a8c9015efbf1f01c36e7bec0d377775a11ef8e5bc86917cbad9983d7b8bd,0x1028ede981873832fb7766ff16ee8c648df4564fca710c8b01305b9592e20e02,-0x4c217c5f9e597216ac6c010fa856228da31073b71cd13a6815e06f492d4b18a,0x13852a187662e83eb1c99605e2f2a3fad36af9c0f32e83dcd53b3e3aa160d9a,-0x4550838364311b3899cbefc9238aa0367525579f38d03e498aa9d2a9c5a6bb,0xd38364899c423316055fea50f7ceae1daf7b555f4e1248e4812ca7754d278,-0x225efe2113a74a6a00e09937c203b53242b6d0ed1540f8c796b058c393188,0x4b5fbb0352bb0ea0059f1bf32e100d8c8bd22068992f16cf9801ecf70238,-0x89bcb7f7a5d7ecd1f97863c0d440ea45f37bf57fa8473f6726c050d149f,0xceba930e874a8d6a35d3c75bb7bcec165ac516bf762b4f4fb862106072,-0xfa716da725a4b622794ac427ed120b1540f9fe80de4999ec491e7c1e2,0xefc5c04cb700e6633f0f44079fdfadb5780188e7ca2e6e0d8d4cefba,-0xb0c6c59c35b287debeb86cdb54da2da9b4c80e027fd90a308e93551,0x6130f680e8eb6645571efef278ce752f6d0190e873cc0d43a52c3c,-0x264459596d34d4851efb081e494a4ace8b2b6662be149b3e98c14,0xa3e4beb5a67cbb1b1e497dd44e76de33fc78775d0cfaaddfcfc,-0x1bdaf1b7c057da10109d1ef625af014032d9a15706c1b191e3,0x2bd3c7e17cfd8769ea411caa11a9f70885879fc0c618bb86,-0x22f3dd4ae4c51421a28266ef9df936d4df25e836f0156e,0xb89b0739f5a0ded2579291b0c5c01dedf9dd6ee2b2e,-0x11c14e3c9b52361a5b100e933320df4cae8a1d2a5,0x3a03f7980c619569988000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 24 86 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 86 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 54 indices rho q25 m25 25 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 54 indices rho q25 m25 25 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r26 : List ℤ := raw_ints% [-0x4d3f46198cbcb8131e937902f472a96a17854d721e66b73d800000,-0x6d21ab601e43a5b4f9f67ab301e1398ce2fad06f24280280b80000,-0x49306bd9b174d69fa3938bf0429c72e12c5b2fa418b5da21980000,-0x1f02326ae086f78c4633f4edf442011184921e334ac1bab3da2000,-0x9513d9238828df009f2de9e3d639b436d450e35a869c97f653800,-0x21cea4b2579f50ad2e821a44a45e02124b5f2ef6b4b62b6b72e00,-0x602f5b9afdb470be5fd3b6cd825620a5793962844aebe8ebc280,-0xdc10692c9eb0f9d19fd8323c5174ff153e889e20331cf7ff880,-0x19bf5e56bc47b40eaa2585ef4a29d76332e80e6091522aaec60,-0x27e9d032c2c16f30669589b6358976fbb81f28e03d34ba52a0,-0x33a797577294729d71ccae7c9e8a22c271593bd17dd0b74a8,-0x381868bb6bf73cc02f6414152f9cf6277aa5181489f9b598,-0x333f537803f16706e41d03e766d508326eb1248c598585a,-0x27649f3a261754d279f7216812cfac0c34b80e3262cab8,-0x196c382625dbbd7d7890ae056435be17fe5a6c0f92e1d,-0xdb5959a624290e4b83fae622a862f096529d7564d28,-0x621241173a89100d2e867cf0aa86900eaa3cc0a2f8,-0x23ef205883b52ad39fd84407fb119b79faacaa610,-0xa9bded941da89be29020f18c46b94344ae72c6e,-0x2763049fc2b2fd00a9d5a05a43f3bf467c1428,-0x6ea9eb4bbbf301c8c1d06fd56be2df383976,-0xdd34aa5734caad4ea2ce36ca3506d63158,-0x118545f4eb2d4ef75c2d152ea1d5bf525,-0xa95172d92ee6e84a63de5548d98dd8]
def m26 : List ℤ := raw_ints% [0x0,-0x9a1e2229ddafb6372b9438360545d85124db106e3693b94b53e3040c4900,0x1057f0f58eec3677727ac23e0f1fa90e1e563e10ea204b2c676b05980b33c0,-0xd6764e529d8c728a9f6e01ad1d0a93a3d48b2c6ad36069754877fd572d0380,0x713d173b46bf8367a0bfb71301fa29bce3716b05e5d975ea6a86a3ed6a46e70,-0x2b422f69e3eed1070248e16e2838be65918cbac2071023ca26866ed2b2448920,0xcbcf2441f269c36dd3eea414949fcfb86d3a0d9ed619353de0a1ebff7dada940,-0x3020d6b87d8cc19e9a87e11b81befae94f4c47b06ef27eec70059d7caebf6ca60,0x95cc08b3324564f77495a773fc186bdfc35c8acdc8a532f1593d1bd967093888c,-0x18785b365a8090222fca3eca2e9f75d24f9308f560aecda528d67a0d397dbb32a8,0x367a96d046ea5304503b696beb3498029ed8859f02e8ea0a329d3ee5906ee300f0,-0x686ff7a7fa4ddfe30eb9d20461e59e6c0deb1a580ccaf35cf288b04c8576acdef8,0xadd5dda674909773f19e7786b19a6b6a1bb89fa00368100f63b41cb07b262cff4c,-0xfcdbbf29615b17abbb1ad5758fec41189d19f6c1f6acc15146d6a3f76cb18faa90,0x143069034aaab0747e614a0ce0620a73e83dae3cec2f03cc007cd830f924d39f4c0,-0x16bcd1a78a6ede624040fbd4328fd8c0c77d0ef43d2ea2b5c46c4469914b9f8e5f0,0x16a38b20be2e2ed282e318e4af97c1a0834e94633a3c6482f75f8516cf4c814f683,-0x13f74c6470c112f487488aa21c8f7820a8dbd1204fbeba3aaa2c2bef9e3b1533f52,0xf9db238d18dc7f7f2b848ed8513b857bab9f75b75a01e8d47aac892cc5e916299c,-0xad63bc2d5b4a955047d79037deb776dfb9af38847ad5094f59c96fb515ad716ed6,0x6abe43fbc821a8d740b45e285af038e9a1d8fd82e4d566eaa656f945120a648687,-0x3a4000190b32ff94cb8e8665eab7ed1f3feca2ef4d4a6ec3a0f295f7dec5859b44,0x1c22f013c3c009c8c4b02991b5972086741d00110a04d74891d2cca2f8a9b8b4d0,-0xc014464d6e05c52b09ff7686e7e4c8396a0dfe3f5df69eafce8ad5d7fb62b809c,0x483141f25e4c07780d1b02eee8af787fb65f505602f5bf21adad5533c48bed447,-0x17d179b0c933d2d4a708a92a4100a1da33b84680df484e0b2c0d2984a478f5afe,0x6de63b3aa9f90244b642905a0a5828ae54b682cac49f2a51567a062a6bc16f2c,-0x1b8f013d6de821d66d7d8c0edf2e5a3d29e1e8d5412e24cd52c379c4ca33538a,0x5f8da958ba0c7b942d45a94dfa35ee0d0a01a9612133bf89b799251e37a943b,-0x11c35e03e847ef4f43ab62bc80d52f1d1a89aef18d438fc8dc4b10ec1d4ac88,0x2ceda8a35bca38aee8e546df443ec7bbf5f58dda823a2ddcbbcf8aa3a83a40,-0x5fa292f818337f555ba08b66bc027bab0c29282c65ce9b2d18a5d23fb7ef8,0xa9375bfe6d2f9508d2a0071e094e5e4292b14ddf8bb79e0728e5a4a0b5c9,-0xf53ba8112770b77451f1d5ed3db19abce574c277fdf920b400e75b7a04e,0x11df6abe6df198542096d2831f092cdeab2ea10a1ff24982aa509a61434,-0x10697907026581ade063969294bc40a7bf3d90af83b77b273eeec4ae6a,0xb8f14c93879cae12658f26cbffba23a197e46802c42787a2c87ce025,-0x60b09d01af555b2f872d084a1d4f201af2d063c27379fd4d8a1ae44,0x24034acb0a0fdd452327f6d4aeb1ffd56d4c4c3daeb5c1ec8180f0,-0x910b6af20a9c67003ab60ca23d0cce5b0dd9bab2f7e102b31a5c,0x1706c69749e2eb1394a18fddfcee41aeb6368aa0280341863a1,-0x21953a5775e022493f177fcdbe2d031c594596d8d9efabffa,0x189c4082b295b277fb8690a94434b236c82d1b66a6a1054,-0x763fcffeccf6ee0cf1641a6e1e3548ea9bec1ac6427e,0xa39c49a778999447ad36518c89bb2906743122a9d,-0x1d9ad7de2f553d4276c0000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 24 88 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 88 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 54 indices rho q26 m26 26 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 54 indices rho q26 m26 26 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [-0xa95172d92ee6e84a63de5548d98dd8,0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r27 : List ℤ := raw_ints% [0xd9eb470e190b8d17b87936215ab9f588db477e5737ee07796000000,0x133c0a6596f24b655cd26e4cf68feaf36040884ce637251133600000,0xce4ff513a6cdbd55f17103b8c78db416aadc29eacfab4add1680000,0x575f5ebfe824e64a436e968beca9417e37804473e7531946f388000,0x1a3dc9cbdeaa38e60973fd299a845298e835aab1694235488b9c000,0x5f2af3b991a318446a8266227eab739eb71c4fa3686a5f370a0000,0x10e9e95d9392e017594e40ea1f2d87d18dd89ec877518ee5269c00,0x26ace8cbe9f1b2025b8adeeff626544516bb0a869847879bf0f80,0x485b4299a3184cd3bf5f73f6e97dacb8f4d2edd31dd1e1e4be00,0x7017a515f7c55f97fee9b72bc7b5ccd2f4e008f82d91343ec20,0x90f6f58fb3ad556e371c19c41228fd7800e1bd564b993d4340,0x9d4edd46b26e42dd04047d6fd072001b46ea5259a6f0c99b8,0x8f98827c6165d1a08b34095b9ba534a017320b50a1c950c0,0x6e4862467ab06cf518e2789fd86d05cbff34c84e5e6e966,0x471ac3e2a8b27603ec4744f935c9917ed8698408b4e818,0x264dd4745acbb0b48d10c9e54af7d578bb6482b946a03,0x111b5220b14f0149aabf9096dc8f6f8485c3eea26d00,0x642ad7c849eb9d57488e4f4767852e3b920419a208,0x1d889e70a4aa2e6f97c2b3633bb6d4537397754b0,0x6d7d8bc074e9d54fb23900615f848d745627032,0x133265e562bd12bd4ee8e3678f9d4d7379ba00,0x264e895af97a03b002ba4d522062460e4b4a,0x30743327bb2dc628c6db42dd3ea4570e38,0x1d3486a656e931323bc120ff105b59bb]
def m27 : List ℤ := raw_ints% [0x0,0x12a9a62311d84710ae46f2ce8aa37531d37686fd589be3701f287d7d7cd700,-0x1f7664c2dce440fba9a569b0c5ca87ec872fce2a0ccebdc3244eb31695b4440,0x19a1b99efcd239ccc1f4754e0113c1f4a1499bc12be0db3e8901c1fae6328280,-0xd70baf7f84b1ba81012d1490b5dd8e1866ee2fd52355e1f1eab2a79bf2657e10,0x518f68bf3dfbcc403ce3b74874df4fd5abe872c4388a5d8c74d34f4339bb705e0,-0x17d6524af64959752a93833e52dbfda197021ea9be1ccdfd0c3457836fad9661e0,0x595d3c19f4ebb71d5fa55e2a63e0fb553d6f0ed821f3f625666f5c6dc2cf3c8760,-0x113e3f180a56910d3e428fe4e18484ba470c01f7f1e4eb364360c0950aab1071094,0x2cb01615ce36773c81abf98a9327a8933f51b8c01f896411b4ee8b7757eb47b7058,-0x629d3c753e9d8245e6fdbe94dee1c1e453f124c39176654b04881a302071b9aad78,0xbb4e9e0315dad6c3fd4167b57e63ba93d7cb6c3c4ca953e08ec1f57c3fcd1f87cf8,-0x134c5f90fd72c303f1af85f377ea53cc91f808075bca6596dcc63f54002e744e157c,0x1bc9dc91f594eb4b23d3ae9ef098a1577cd2c36a111dae3e5cb3eea4cbb926a5b2b0,-0x2320169fc2d571535ef42d4e93e19d9bbe3e62fefa450b9dda4a1c73ac2a8a5fd610,0x271f205e11f045b7a271349adcfd21b4c5244a5009c03d651ae3351cf219f87680b0,-0x267fc87298b2346c8cdb0f3ec1c2f52d6f87e136d289d270fbd886ce8cdbefcce9ed,0x2189f90cda73de313a6866b0ae6e1be9340f8e6027ce03dddf827f79350ff14129ae,-0x19e4f37dc04ff9a6f1b11a53390283dca9f1f786964c5a74b8d63e15784352fae666,0x11b9d05185c370f09711b58f485fe054e3e32a76b6edd111c7cf3cedf2c449b97a56,-0xac1955762f7ad6ec01429a1e944e12ee341af9a1d39d56f9d526f8f93338dbdfb93,0x5c7df816f4f6094a686f4bfd76c43c40e2fff73f880b33b5febab5129a474e04c4c,-0x2bf59fd23d726090bdafcf81b56d67e86f2db5c27093cfaa64ce24077069d1202c4,0x126fce2e3141e03fbd854c543dc510f225e55e511f5da7857f8a9522c214727340c,-0x6cdd067490511eccf4e13d983ab6e5ede6ab25f198c53cd3880492d832b07d013d,0x23397cd412b445f52eb66da676d04ee1fdd903ab558384c4dc407731d4671e5732,-0x9f2f52944687d21e34ee14e1702c0dd51b5e0825b0c9475e6a5113fc1fda7b9d2,0x270a09f4250a71057c3965cfe86821660ec4027e149a9d3f47c8eb3405b2f669a,-0x842adb4bcc740d364b3e4a685ec223d4e702d576cea64e8c9ffa22245910c98b,0x17f2747d798c31600b4d3ae2e629a68926c1fb7b0dcc32644d6ae71f4459cb58,-0x3aeaa7f2536e1660c67fdb90db6693e4e4f752fd935caf135f9d83c05a07ca8,0x79b741a8d2cf986d297fc477749a756d3e0130ea60d9f6fd8d70bdf1c74e18,-0xd07ea61e325821576b1269ad3d66112bba7e6d597ee82ce37cbd1e4eb47df,0x123b215cf8772bb0e62ead32cafb7e5dca5587ecdb5bd017216943878d012,-0x14753211f56fe0faafaa62c514b0368c2e7b237612cf2c7d01dbee596a4a,0x120356078fb68f81298c16e7a48e384e5191b9fc7b29b96b058566b590a,-0xc1d830f8fb0a881f622f3c55f81456a178be90e3ab29ab195448a8f81,0x6055fa0cc34d6142a6a27c0ce6568f9be7728c763b6635de1ee9090c,-0x21ee1d046067d7d230ff899d5a6acfac456da818d4eca129298d064,0x80767e3826075b2e5d5d6e17a5e8049b017c635873aada571cf0c,-0x130b016028f435bb6186b87ac6eadd4f13fbbc1e7404d0a98c63,0x19bc94c6b6e0e8e2bfec49b12b8f831ac5d3d55becb70d6e76,-0x1153aaead8270fa1ac531d970fcf0779a4c10380becc7c06,0x4bba64338abc40dcff80c401a517a019d12b5b40f8d4e,-0x5e3424997eab3158c2f91fac487167ac92990d47d5,0xf1aa0e45b4a7fe6f9200000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 24 90 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 90 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 54 indices rho q27 m27 27 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 54 indices rho q27 m27 27 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [0x1d3486a656e931323bc120ff105b59bb,-0xa95172d92ee6e84a63de5548d98dd8,0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r28 : List ℤ := raw_ints% [-0x25969460c6c46ca2b8dc8d6ff6efa0dd4fdd6cc072092bff8f2c00000,-0x3510981b0be1f45702a21dc801dadbd9051a2bca572878ba8981c0000,-0x238f7e4672747a37ccbfe865063cd73a92b8b549e470fe6dab6e40000,-0xf0dc13c3feb21d35d5be63c52f773b01680a3691b547ab1bd0321000,-0x484ef8eb2b65d8908b58486afde1bb464d46a52266b982efbc79fc00,-0x1061da7c990899e071629b52c2b945c7b17226b5fdf07b32a4dc2700,-0x2e8fc89724bd82d93f8f17d14affe168188b0920af8c3a87b27b940,-0x6a69bf0768aad379e423aee938de3b8ea8186d013fd24722dcbe40,-0xc6f8bb1c2dbf33084a6838ca215c43d68249284e106dfc3d70750,-0x1340d8d3400002c1d89b5a19041ff060bda2af1a3fc536ca09d10,-0x18e21ea5cdbcfce36f7f4d6c9d30a3527d5baa2940b8903d269c,-0x1afba9a56f84f08b6abc6d261268f65010dd692207a982f5e8c,-0x189cc3b008dea6a10ddc2bd1d5fb6452ec853c129c72d36f13,-0x12e319a25079fd5738e418594f21d7d1565db90c49294d778,-0xc2aaea9f1d55f77bcc558686fe39e709632c424124d3cf4,-0x68c49d6660d4de3c95d54153fc248b4a29c2ae9f6caaec,-0x2ebde8050ae1e7c748579ed517ed15423e6e3ada28542,-0x11163cfbc9e3effd59d815914a837c0afc69a573dba0,-0x508290bc59e2da88f4393ffdd39ab7262b4be3dd50,-0x12a159b1c9b55a141fc4cfe9f1dac4bd4f4bd3ee4,-0x3430336241055200f27106902769bb90e402193,-0x67fa4f924810898f537fcaaaad28e6c9a5698,-0x834bc0f34f4834fd3fc3970d7f4968bcca8,-0x4efd3005bb487c70e61cd750b42a8fba4]
def m28 : List ℤ := raw_ints% [0x0,-0x2428b1e3f29309b051a976702c9cb31089b5a58adbae08a93c5e732321e0900,0x3c93e6cad8f019e188e4ad4c7f2322107930f486de4ae260aab94073c20d43c0,-0x3107f5ecd4699fba2a8c537f9ad2f7ea1923a1b94412d4c48d0e5741bd0c34b80,0x19896aac1047e3b015e48688866783077d0181422e3632954f45e7540b0c59b870,-0x99e0debc6019239b3f1cc1a26a923d8890e80d6b4f9619ab5b6be1cb9356868d20,0x2ca5200bf9cedfbe4afc16fcee9178c85941c29625b6f90c4536b0bb91ce995b6c0,-0xa6194ee30cd43f04615c2fc8b778e93a9f23f246b0a4754511948d6cf8ba0485f60,0x1fcb990a3cf6ec087c04985038fa8136b0c1c2369fde1ec80c55a380e069289fff8c,-0x51b84a563ad427e3aaae868036eacb615031c16c5c7d5e91e47b4cd744260c97d7a8,0xb2c694a8154848d67b755223f349126ad062b9facefe34fcf42a531c99a8b5bc3250,-0x1507f43715bf33823c9781c7b76c8291828ce021011f86e20653e28ebf2093eb8f038,0x22577214b1cd26664ce4d9a77e5e8baea060003124bab59b48f8092eed6df6f76644c,-0x30f5c26c87d26ff1e93f533970dc4755c355aeb9e8d20c3c0e26ad0caf4e6e46ccf50,0x3d3e5001025de531a1bc2c30df81b0439a74f90e902b294896de3713117567ba80d40,-0x4377784fd7e26dab0e783e3c2afbaccfbcecd64429c7a009dad832da0f5c5d7902c30,0x41a1a3fd4ef979038e6e459108fc834a375ad6ea9c0a52da5c3ebdd8ea4ecebd01c03,-0x387c1d66c0cd90ef16714ff08d9d076366b51e6df9b14d1b08ecdca7fabc0998d5a12,0x2b0e03db9921262930101f93329d20e973736f8c02df5d90b08d2936012d0b0a4c854,-0x1d13a228ffa808ec5e2ce09c2fa3f1101616ef2c31ae4d232ac1d9cf87d6b2acdd7e6,0x1164aa3f30c1dd6b88c428074b5d52ddfea57a6973e30c2977abaafe3bda7bfc34047,-0x935023316602adc44d0cd0124084c86e0d1133747dd03008022c7874760a86e39eb4,0x44e5b3225dc58e7e90f1afadf79672dbff0cded087de8a2ef1d749396b10ca0eecb0,-0x1c67e1c6f32e8162a6d2841eadf0451d2f36365da9e89e1ce2e4063c332ae28ea66c,0xa4b36acc3a19d06fe054a3c5dd6c73cbd595792015cf04ac4ee10d6b2550ad4c557,-0x344428f8fbd230b8d142d70dde02b63d39fa45a7d0085cd8a1b21c52f8f9599268e,0xe757b9a056741db1ec1c6529b8376f0494bb9524415d44f096c6ec1435a24f7cc4,-0x377c9704d6655dfdae1498cbe0a2aefcec061223b3539b798256cdf79887eecf0a,0xb769e319c2e74ae513cfeb902aa9fa02ae2979093e440b65f0e74891cb8f9982b,-0x20635e00cca541966243a3c9e352825f20142dbc2162fb167cd6808e27c669ba8,0x4d808cb9416403aaf5ea5c4c66d1dc988d7ff92d8b4de92b7e13d5a0150c6f40,-0x9b5fb91cf52d9b11ff05f4b00aee8a363cb13898885fae66cf31d4ad99445d8,0x1019e10be361527bee134e5dadca69c43d89a2ca9f48e26dbea420e003034e9,-0x15bded052ed59c0eb5fb03480c1e9c4b1ab350a6766eaa7c3a0132fd9c422e,0x1778e9378b0d54e1719e8c830339fc41466a621adb34057c6ea7f122b991c,-0x13cfbd64e619068a1acef63d265165edd31b347d5334095324a3d7fba87a,0xcb88ae411fa7094bc1e3581ad7264f5616134df02e96f1bf172a09d8c5,-0x601ea2712c50576cc053a153f8a3a4c2ef22374f76a330de040c7dff4,0x20007e057059d97147d6ea4a16fcc90e022a3f438a62370427c5f210,-0x71db9e1beb9bd68cc8a9703158a02b34d22f3f71a198259384dd6c,0xfc134394518cb5bbe96a5f7e7ba7fe549f9dc5ad71ce999b23f1,-0x13b9c596615c9f0747c3eaa49b61f94fe257aaa1128e72145ca,0xc3299fd7df4f9e986a5fc0a5738ae4a626595dd3395799bc,-0x307c8307a8273e6d76552c1e188e541844d12815abbf9e,0x363a18eb57201dc51ae2d340801b52e3741eef8f84d,-0x7b44e62e6fc0495cfb000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 24 92 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 92 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 54 indices rho q28 m28 28 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 54 indices rho q28 m28 28 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [-0x4efd3005bb487c70e61cd750b42a8fba4,0x1d3486a656e931323bc120ff105b59bb,-0xa95172d92ee6e84a63de5548d98dd8,0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r29 : List ℤ := raw_ints% [0x65a9745f67f67462b64e91a087999fef926ddf6feedf14ec4799000000,0x8f79309c88a072ca7451c26f2e3eaa36ed81163cb14db2b4a0f0100000,0x601cd6ce83b41d2d6f628f383278d242468943f1c1a78b062a25940000,0x28abfc0d3c8057973b9cc8f99537b1feac8e5afe1fc0b49645b7fec000,0xc3486995cdf129e28092ca25f59964dc67dddc9e4c66f280c9ae14000,0x2c396d3c363d43592fcb7e89977704e03633cc03ce7a136127b373800,0x7da2f608d08c7ee17178646cf1cfb159836452716b91672b20cfd000,0x11efda9b53a7c51d5b3faaa364361e625304c14cc0f2d8ac411269c0,0x2185529c5a8202338ac6be03a9346cb442bb88f407790cc6f767580,0x33de4841903801fa3d53c19e5ea087cc71abe350b8c084fe138770,0x42fe9c45bd7f06dbc2836ef67d063fd73909dfe6e3cab62e4a140,0x4899b47e0f4fd4f914fae0c9a931f9e07a8a89146b9233d59674,0x422ce0bbde87f1d992136de4ada62847d9b75be2a4fcea89bd8,0x32be51c6c788acea8a30c9efce231392e8a5eea1c8986d668d,0x20a950ce014a754935e6cd3156bc3fafac5303d9941c16900,0x119005fa240a95a9ecec1ffb2dd5a680ce49fc28197b61bc,0x7d3fbbdbc86573d93bfbe92cfa00cd5aef6ab783596570,0x2dbd2cc0ffa65814bdde6fbdbdcc3b07b67151940063e,0xd7463deaca41a09354c74d7c3299a563c0da5344380,0x31c15bdd55d44eb3f251eb31c9915f5f7f41838220,0x8b3212f2172964d01179b2fedf77638ed500ff78,0x114eed613f6ee507d54402285a689967765148d,0x15d25fc6f8c2d9d0a29ba827b4a6d9f9a4c00,0xd1b1ad72b184e8124e922920a146603b28]
def m29 : List ℤ := raw_ints% [0x0,0x460ed8a9a5fce2c59e385579566f9af00acff0bd09a130c7e4f6ff1411a31700,-0x74a7c5d9749e2e999b9ceabf762c30158aeef94d6cf671b1a0fc5f2147f9b3440,0x5dd2a30c62ffb9708e99304cf94cf0ecc6bb2eb9f38f207b78efd3c9608a656a80,-0x308b4e6e5c09dcf170c843f01c3333077936b997c468b3a16f0b48f92deaa9d8810,0x1228329d2aabda94184e6f8d4e8d592999e61a945445e84b35e8f1fed114261cd9e0,-0x53af83a76ce5a6e560ddc2bec637cf88455719b9da14744d755f36e591e52e10b560,0x13507e2c1c09375a25bee7cf102ea9d13c9c1b01a159d73587edec318efa4f3244060,-0x3ab25852de9291b91ed0c5b552f9b2ad91a06603054d1a259a525da81e139ad0ade94,0x95a3529a689ba4bd5dacf469758688580c4cdd46fed703f82db5eb47f951b2b4dfb58,-0x14494f7c093a18657d3cea326bc762e55b54c048e51e328dd11ea2b7d524f089d55a58,0x25d841531219dd683d7b817247e8c5bbd2f5a19b065e940922870ced48eb3c0fc47538,-0x3d38d331a77a67c66ff2ba92567ddd02ff67b5f134e07b8a661ec653cfa64a739f12bc,0x566e74ba2b0b2d5ce1402bccb5442c451a73567c754ae10ef2a8dd7ecb4938835145f0,-0x6b023c102484d9908b03c74fef1af0e1f9c1d724e549c93e6fe7184dc6b987d0ad3f50,0x749cff1af2629ee01fa23c2e991676c3f21e020d3a45792e864ce3fef549b787d5b8f0,-0x7027cc87982fca397cd932edbef48c7da7d1d5f0439e4aee135e6df80c1faae85321ad,0x5f5f497173626544af03f6f6a007df8c6995ba325d0a181639f8e1ba4cfdba163633ee,-0x47c79a0f2c294eb488f4d38d20a5639db468e5557ffce8c138a203f7784ffafbd4f0fe,0x2fd47bfae760b068ce819fa73f16660739c3704916c46617fbc06cf6964e7c0f16f926,-0x1c352b62fee166449831561883de020bbbc136902ea0364500660b356a5d2468df8b23,0xeb55d812af91ebc6c4cbdddf9c303f34d6d7e9c06f89ca2ce880853644603df8481dc,-0x6c5146893e5a0eb29de2b7d3befb3219034ec18078bf68de3bf05b7a204c0433c3714,0x2be7859a113270976d0599e878c73fce9e8e544a98a28fe21c98c270d0ec63d297d5c,-0xf9fbdccbaa11c77cefb1a5c889d748cf7a01cacbb34c473cba0a78aa4b70af3877bd,0x4dce6689fbfb7384afcd9d2d55e3b8a99e7da693cd5ed810213eadbeb83805c712e2,-0x151501b11b279dd003314889697b6d8b7d09957b9a390df2e1f971a2d491c95dc35a,0x4f1f1d43b90d7ff70a8398d149f9f163c5cf7dea17cb8755bdba3ea1b0da62b289a,-0xff5a48944c56f88c8d680dbbca076ae2252908967dbbd0db6e1c97050953282b5b,0x2bf173e7893c7d73d57e25a15c27872227eab44c17400c426abd035a41b2856538,-0x66434223f5fc887169f37a98f96cecbca11ab7878696868d5eb078f2ca472aec8,0xc6eb6944374e142a3251e7965fdf149b2be78edd694aba15f555827f4a4512f8,-0x13f3077715ae7463f459e4894e15691eccb7065aa8534d4ea02a71841739571f,0x19fea81fbddc46f2dd90a997bae70f8266d46460e851824ff09f742320d4eb2,-0x1afe1bcb4cdfed9c1c8838c0eec8fcc7f272be79e05d433ace4039b363e3f2,0x15d5454cbcfeea566e67074ab4ce01694263d4a8ed1cdc77a490aaf276eda,-0xd61142c6fb4aa026a2d7765cc8e9135d623e116237b11d382d9fc7e90b1,0x60086b73fc55a825e2f2fa6ceea7c386ab5c9f6363f51fd62aa541435c,-0x1e369da7e7923bbc501f1c08f69905d330952973dad8177e9c4fc6434,0x64fab998c495729a7d30422ae3618f0e35a7977271590eac9d2389c,-0xd09e71b9f1949080764fddacb3cf602e8ae4117ed1556260af4e3,0xf1eab797662bda0da557511ef2eb19b2e8e010429bac08f6de6,-0x895fcdf8e0ec8af94acd7d81fac7365d3bdd53f341e8f9a5e,0x1f09967d332b9775f1ab4fab4651fd987297fe598ed6d6e,-0x1f350ac5391b2d7fb82fba9362add5f43adaeb625a05,0x3edd7e4dbecce9bcb88000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 24 94 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 94 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 54 indices rho q29 m29 29 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 54 indices rho q29 m29 29 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [0xd1b1ad72b184e8124e922920a146603b28,-0x4efd3005bb487c70e61cd750b42a8fba4,0x1d3486a656e931323bc120ff105b59bb,-0xa95172d92ee6e84a63de5548d98dd8,0x3c04f0613c14a5a0ea1f5c87346d6,-0x14c598abb5140cc3879d7dc0e7fc,0x700b849bed4d4e3d4b2f8846f9,-0x24b36a30bab9ac1d0c308ba50,0xba52fa1060e6bc1b17db4a4,-0x391289382b4de44d6e1d14,0x10ceb9197f1fc10bde057,-0x4bc6b706f67b89da088,0x14501fb6cddca5b092,-0x524e19e9bcf81cec,0x138551fd9d711d5,-0x44a05eaa6d280,0xdc60e802aa0,-0x27a65ce584,0x63ac3c73,-0xd28338,0x15f0e,-0x19c,0x1]
def r30 : List ℤ := raw_ints% [-0x10de267f03d415a94c9f37451a8b73844befc1fa9645f16d4aa6aa000000,-0x17cc3dcad1eb78a708912cfc0ff78138a0748259f5ec69bc3c322a200000,-0xfefd72de32755e0e136327372eed9f1afbc29939b9b364f9390a9d00000,-0x6bdd998b7985f67be13aa668458af4541d286943fc46fa3f0ac6c4b8000,-0x205b6be227f3a5fd2017a542173a93457ca905ed6d4a9beeacd15c16000,-0x7532160229c005b259a27c527a62b8bffd085b49e20d115d65495c8800,-0x14ccbe4304ed23c19a25399cf05ca4622e0444cc6ba8712abdfe30be00,-0x2f7da79a75ca276488cf6cda606a7862e65576b2a4e4e2c95cbf61e00,-0x58b52648618cba1d27d811e87a9a897246d2b601bab91e6d4f37cfc0,-0x89304a9fd0b1855bb75398bd669a3a1ba8b5b904793548b29486200,-0xb11896dbe332db668ea6144b24322debb72a3cd42c0f7f8d31f6b0,-0xbfcc392c9f909983144ffc8b1a76378b1239013bb1102aa2a1460,-0xaeb5982cdb094ef5ca352676a266f24ce39bf4f2148a0beadc34,-0x85dfa17445aa3035c87a69e198cc2d3612eaaebf67269208a68,-0x561a869df7405b011772f2fc542d864c9c6980c03994d744a3,-0x2e43026365a5db5f97526a997b9898a788347f226cb032ae0,-0x149a1560f82b91dc5d1d896dea59e65401ff3208bcb51b1c,-0x7843142aeb2a82c7cbc49254f5e4c928d53b2d45133590,-0x235720aaa71d8ed643d036679ee9c59cdb6f3de4cc702,-0x828b4d5285d07110e9890c70ccd2d46a10a89fe7be0,-0x16cc5dce1355839a1737dcaa460142ec72314b66b8,-0x2d4c771e5686483bcb2453818d7e70df821503c8,-0x3907b8feb0d630f4c3ae18c6770ff48f1191e3,-0x2232d4a620595b374de8b0b45c670851d920]
def m30 : List ℤ := raw_ints% [0x0,-0x87bcc3c8b199f75ee28d259b17783c3114f2e26e42a84e834b9e8e36e22bfc900,0xe0ae55e02482d3a44df7816a0caad592496b3e253bdf8712098d2e8a5b73cb53c0,-0xb397673542da95ee3c1f7c4262da476b295088f987dcfd1deffd083c54e51f2d380,0x5c532eec17f0773fdcf527e2017b5c2264e49699cffd4e8ce90dc624750b9dd93270,-0x224d320164d2360fe4a5ab15504c5a70a829d197959fa4cd60a2e18ec1ef3626b7120,0x9cfe558cd2e73ae9769380471795ba6efcc4d1dc04d2327965c6cd97c0237273a9040,-0x23f855eddaae7abdfd02c94c733ea89436e27188c0633d5a493971316cb3cd700b1c60,0x6c7b7a2839fed73e879770ec1b47bd8557b7510a2ccccb7d1c9859250618af04289e8c,-0x1125c520004508474e2a16ce1c8ed122dd1f0abe71751b3648935b8419c66acec8ec4a8,0x24e2b2bfcc2c49f2677fdc0687c3c0a1815b9f138806e7a190cd5388597ead2194d0eb0,-0x44360d6347b50c64638d7b3eedba0617e7bd7e065f4259eeb92ed489e546a2a1f142b78,0x6d5658fb5f98f013de0a4d4f4cd465c82f85fad96574a6dea62fbd52e3d6177f3473f4c,-0x98e0a7de3f4d1322f4161b2e2e206f16707f097d39fa5375b19cf34b439abd5ede5ae10,0xbb5d31b2a1ef774b2ee4812980d55e3995964e641f795cee8e7328ae0819432533309c0,-0xca03244b97ec8d133695bcc29dbd17e60b7b2909e94ab28506ac97f4d26f0a346035070,0xc01d874408d1b77b825081b805e0bfd4c2f20012f96813f67db4d99f3e44e5ca9fe5f83,-0xa16ff3d25ebf5edf9e265fb6b24c7c5df6768421ab2187575e35e24424a114fd85b6ad2,0x77fc60cacb00f31850834986f7be944c8eb39fd45497b4ddb426bc23f73fbd0f9ecdccc,-0x4ee56d67f5e50b27ebb066afb01914c3f355967a2b52cd4bde81fa63fae0564d9946976,0x2de0ba0dd26ca8295f6b749c09343a33415bc91999585707514f33dc71c849d10f49187,-0x179124f70e6e7fa58a8ae09a4a91aadc39c9c13f661e04b4fcb890341e258b3e8f22ea4,0xaad0512c61c4a919c70426f5b6801202baec844248760553127c32b3e5287bf9a37b90,-0x44125e1347fc1fdefbf4361469f77a4eef20c217c420f92559fb0829674b69d7adf9bc,0x17ca294c2c1f370cb42fdcd4e68217f4ffefc0e1876d73fc407f3e5c6c39b0a0e90fe7,-0x7432f5c34a6bc70bf8317648c88b60524e67470084af6b9e01f6a662f61907489059e,0x1ed6975f92c172b2f3b2f14fdd2e74c63162042cf8ef3e5dcbfdbe2de662cf9a0f71c,-0x712fb2418f7e6951ad2bbf1646d81571a7487872fdddeeefd0d6117d02dfa081cf8a,0x164a2965a5d72a184b6d2dc3a963604519b8a22dc7b72ad017871d3f68da2029ae1b,-0x3bce2b7ae0afaf42cddbc24e8e316f94e822866db30f2657d3f8d7d10a1900731c8,0x87566e88ba3dd273406fdc659a359a8565664467fa1d8f32fc0d70c99655139c40,-0xff65429896445c2c09b6f195b5bc345644739d441ecbfddeb36989741b92135b8,0x18c88c21eeead4f1f37af986411bd59a72fd5555662a2514f677702bfa6815509,-0x1f27e5fa3f0d85152ab1cc7f89f8fcb6eb9ba224bf9a6ec5a3a291ec7d74f10e,0x1f1bfb00ea033984cf90c6082e53ce76caf4eee7370e76ce3527f74f4c70544,-0x181b6c4390202dca4023d433b1daecabd98d0b62c0a4fb1aa302cfebc0b50a,0xe181c56e9e61c9af43ffa8768f3f9105b5457d6f12508d6d622e2d6434e5,-0x601163005de3ba4e869c436e2081a5f0781fea14b268a407816a1497c24,0x1c8d1c89906186395b3dcbb3363d3e1b24e86679568cf0557e1cf44430,-0x599c7dbb914077b4670826ae9089652ba79550cecc0f1ebcde1f4bfc,0xacb4cc9349d616c3b020c9eb82ac084facd642e51199f4d5ce5bc1,-0xb970b99c9d094fae85995867c9c372c15223e59b5dbe459c351a,0x60af6f826e55f73ac5d6901dff3d7af96b8f08ad558299ce64,-0x13dd0e8d77a1dcb0b1a6bc70c64b036ded3d5cb7e74d0abe,0x11f48390eb75188d64b02e60d6901861e2ef6d3dd5afd,-0x200dd29a80f827634ac0000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 24 96 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 96 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 54 indices rho q30 m30 30 455876542810304656602005283840000 31=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 54 indices rho q30 m30 30 455876542810304656602005283840000 31 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_30
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<31) : intPolyRF (mz e)=rfPoly (C (455876542810304656602005283840000:ℚ))*rfX^31*(1-rfX)^22*momentRF (key size) (X^e) := by
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
#print axioms moment_source_30
end
end CatalanCore.Li2.NVMod.FamilySource.V8C32
