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
namespace CatalanCore.Li2.NVMod.FamilySource.V4C13
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,4,13,size⟩
def bases : List ℕ := [0,1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12]
def num : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x4c22a00,0x60aeb40,0x35a0720,0x111074c,0x36f6a8,0x74391,0xa170,0x8e2,0x48,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x14,0x5a,-0x3d4,0x1324,-0xf810,0x44e8,-0x15450,0xbf6d]
def rhoDenominators : List ℤ := raw_ints% [0x46,0x7,0x1,0x1,0x1,0x5,0x1,0x7,0xe]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 13
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤12))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤12 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 13 omega4=padCoefficients 13 (omegaCoefficients 12 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 12 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 13 omega5=padCoefficients 13 (omegaCoefficients 12 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 12 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 13 omega6=padCoefficients 13 (omegaCoefficients 12 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 12 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 13 omega7=padCoefficients 13 (omegaCoefficients 12 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 12 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 13 omega8=padCoefficients 13 (omegaCoefficients 12 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 12 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 13 omega9=padCoefficients 13 (omegaCoefficients 12 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 12 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 13 omega10=padCoefficients 13 (omegaCoefficients 12 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 12 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 13 omega11=padCoefficients 13 (omegaCoefficients 12 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 12 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 13 omega12=padCoefficients 13 (omegaCoefficients 12 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 12 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x8,0x1c,-0x38,0x46,-0x38,0x1c,-0x8,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 10 li0=padCoefficients 10 (liCoefficients 9 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 9 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x7,0x15,-0x23,0x23,-0x15,0x7,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 10 li1=padCoefficients 10 (liCoefficients 9 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 9 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x5,0x9,-0x5,-0x5,0x9,-0x5,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 10 li2=padCoefficients 10 (liCoefficients 9 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 9 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x1,-0x9,0x19,-0x19,0x9,0x1,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 10 li3=padCoefficients 10 (liCoefficients 9 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 9 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x7,-0x1b,0x13,0x13,-0x1b,0x7,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 10 li4=padCoefficients 10 (liCoefficients 9 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 9 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x17,-0x9,-0x5f,0x5f,0x9,-0x17,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 10 li5=padCoefficients 10 (liCoefficients 9 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 9 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x37,0xbd,-0xf5,-0xf5,0xbd,0x37,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 10 li6=padCoefficients 10 (liCoefficients 9 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 9 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x77,0x42f,0x4c9,-0x4c9,-0x42f,-0x77,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 10 li7=padCoefficients 10 (liCoefficients 9 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 9 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf7,0x10c5,0x3d03,0x3d03,0x10c5,0xf7,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 10 li8=padCoefficients 10 (liCoefficients 9 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 9 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x9,0x24,-0x54,0x7e,-0x7e,0x54,-0x24,0x9,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 9 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^9 := by
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 12 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 4 13 at hb
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
theorem cache_li (j : ℕ) (hj : j<9) : coefficientsPoly (cache.li j)=liNumerator 9 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x2841068c40,-0x1ef59109330,0xb02407109b0,-0x266040644d3c,0x5b8ea5e5d71c,-0x9e23140f5700,0xcbedbb1f5340,-0xc78834028877,0x94f99cc5e8ef,-0x549d03da3b1c,0x241ed722bb2c,-0xb53a035acbe,0x282d59c6fde,-0x5e938935dc,0x84441ab0c,-0x581bad67,0xf80baf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 9 20 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 20 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 22 indices rho q0 m0 0 49392000 12=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 22 indices rho q0 m0 0 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% [0x1]
def r1 : List ℤ := raw_ints% [-0x4c22a00,-0x60aeb40,-0x35a0720,-0x1110728,-0x36f624,-0x742d0,-0xa0e0,-0x8a8,-0x3c]
def m1 : List ℤ := raw_ints% [0x0,-0x1e30c4e9300,0x16a90caf9e40,-0x7da0f4718640,0x1aa006ace86d0,-0x3dab5a7cb19d0,0x672c40949ca00,-0x808811da4f480,0x791be7f4d0794,-0x56bfd7f693234,0x2f0d05362e150,-0x1311b7a826310,0x5a279eb40ce8,-0x12a4fe5878e8,0x285c57dfc50,-0x32ca800010,0x1d574a2d4,-0x42a4e34]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 9 22 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 22 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 22 indices rho q1 m1 1 49392000 12=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 22 indices rho q1 m1 1 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% [-0x3c,0x1]
def r2 : List ℤ := raw_ints% [0x11d81d800,0x165ccf900,0xc30ec040,0x3ca3aeb0,0xbd0c838,0x17cdfd8,0x1e9370,0x17418,0x838]
def m2 : List ℤ := raw_ints% [0x0,0x16a493aee400,-0x109c6373b5300,0x59de273f94900,-0x128db2c9b9c3c0,0x29c706eaaec540,-0x43c9c8327f7080,0x51ae28bc787000,-0x4a32366db826f0,0x33087d06fc3bf0,-0x1a7329ead80ac0,0xa2e6201221ec0,-0x2d5a87ca2a6e0,0x8be4c6f95960,-0x1160a6fbfc40,0x139e7fbdec0,-0x9c81c13f0,0x11dc7af0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 9 24 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 24 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 22 indices rho q2 m2 2 49392000 12=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 22 indices rho q2 m2 2 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [0x838,-0x3c,0x1]
def r3 : List ℤ := raw_ints% [-0x271bc93000,-0x308c3b9e00,-0x1a261d9600,-0x800e53860,-0x187178610,-0x2fe28780,-0x3b1f0a8,-0x2a6e00,-0xdba8]
def m3 : List ℤ := raw_ints% [0x0,-0x10fb6ec32b000,0xc31a46bc6dc00,-0x40783391748600,0xcfbc54a3b78700,-0x1c7574fe830c980,0x2cd79b0dab50480,-0x345200a95426000,0x2ddd5b7a2857140,-0x1e51786b5e1d940,0xf066ebc43f3700,-0x57e9fab492b200,0x170f3bcc4ebd80,-0x42408f9ff7200,0x78b03ece1680,-0x79de41a9e00,0x3433fe1c40,-0x4c6a0540]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 9 26 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 26 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 22 indices rho q3 m3 3 49392000 12=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 22 indices rho q3 m3 3 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [-0xdba8,0x838,-0x3c,0x1]
def r4 : List ℤ := raw_ints% [0x41539599000,0x50832a0f200,0x2afaaf16f00,0xd01e4d37e0,0x27282e5de0,0x4b479dc18,0x5aa23a00,0x3ed39a8,0x135940]
def m4 : List ℤ := raw_ints% [0x0,0xcbc9312604000,-0x8f6b913446f800,0x2e6025a2ae04600,-0x91f5b6f658fea00,0x137d525649a08980,-0x1ddb85fef343bb80,0x21c5562f85a70700,-0x1c98e6da3f320800,0x122ece62afe70480,-0x89f0e6522825f80,0x2fefd8734ad0e80,-0xbd7de021445280,0x1faabcfa7dcd00,-0x34c69ab3b5700,0x2f8425a8ca80,-0x1169c28d180,0x14634bf00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 9 28 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 28 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 22 indices rho q4 m4 4 49392000 12=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 22 indices rho q4 m4 4 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x135940,-0xdba8,0x838,-0x3c,0x1]
def r5 : List ℤ := raw_ints% [-0x5c11cf248000,-0x70d58aea8000,-0x3bd177baf600,-0x11f30f7dd000,-0x35759a8da20,-0x6563e2ef60,-0x77f1e6fe8,-0x513c9080,-0x183e058]
def m5 : List ℤ := raw_ints% [0x0,-0x98d6e4dc830000,0x69911441fd6d800,-0x21726c59d583f200,0x66f40644240a4a00,-0xd6a59576ab3de080,0x14015e51f75c2be80,-0x15f57589b802fd600,0x11facf3957cf07400,-0xb012b9755d494300,0x4feac3bfab783300,-0x1a65be2502e77000,0x624227332100400,-0xf445899eb05480,0x173bb72ccf8280,-0x1297b6b72dc00,0x5ce74933200,-0x56db6b400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 9 30 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 30 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 22 indices rho q5 m5 5 49392000 12=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 22 indices rho q5 m5 5 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x183e058,0x135940,-0xdba8,0x838,-0x3c,0x1]
def r6 : List ℤ := raw_ints% [0x735b1057e7000,0x8cbbb74345e00,0x4a33327a3f300,0x161dbd4660c20,0x4153fb31f9c0,0x7aa28283fb8,0x8f35e68f20,0x5f6505dc8,0x1bda8840]
def m6 : List ℤ := raw_ints% [0x0,0x72a12ba56240000,-0x4dcd163fe7b58800,0x182ec6df9e5b22600,-0x48e36d821db90ee00,0x9479c2d6d6beaa180,-0xd7c38735652636b80,0xe613a5dd446558300,-0xb652bb78da5773d00,0x6b8050518e6c87c80,-0x2ebb672149bc75480,0xeac8dcd4ce61b380,-0x336a5e9653630380,0x76b71328f20ac00,-0xa4a21f82e49200,0x74bd8927f6980,-0x1ef5acde7780,0x17152df000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 9 32 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 32 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 22 indices rho q6 m6 6 49392000 12=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 22 indices rho q6 m6 6 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1bda8840,-0x183e058,0x135940,-0xdba8,0x838,-0x3c,0x1]
def r7 : List ℤ := raw_ints% [-0x848a4e1ada8000,-0xa119a25eb66000,-0x548f77a7566a00,-0x1911a363364000,-0x499132f70dde0,-0x88ffb6fdf280,-0x9e677239c48,-0x683547b960,-0x1df25f438]
def m7 : List ℤ := raw_ints% [0x0,-0x55f8e0bc09b00000,0x39680189d6687d800,-0x1186a9171bc3cba200,0x33c958ba6dfa104a00,-0x672fd8db2585299c80,0x9249a4a533174ae280,-0x97b2778bed823f9e00,0x7472dc585d8514e800,-0x423118159604b86000,0x1b9263b87617aaf400,-0x83b29f99ba1a01f00,0x1b22fcf775d9f1b00,-0x3a20863b3c9c9f80,0x494e246cabb6d80,-0x2deb062a210500,0xa4ef9e12d700,-0x61f9154000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 9 34 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 34 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 22 indices rho q7 m7 7 49392000 12=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 22 indices rho q7 m7 7 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x1df25f438,0x1bda8840,-0x183e058,0x135940,-0xdba8,0x838,-0x3c,0x1]
def r8 : List ℤ := raw_ints% [0x8e801302c813000,0xacac9366001f600,0x5a4d8e81365af00,0x1aa75aa11539ea0,0x4dce070a2fd4c0,0x8ff6cd1811dd8,0xa528c8341e00,0x6b9b7ffbd28,0x1e8d64f660]
def m8 : List ℤ := raw_ints% [0x0,0x407aa88d074400000,-0x2a67c2bd30bc9a4800,0xcbaf77266a5fadf600,-0x24eb20d1bee3213be00,0x480904569ad1371c580,-0x63bc71074014b96ff80,0x64ad59b6cb6b0a85300,-0x4aee3c101908f618d00,0x2916f45ab18369c1f80,-0x106859ead09f0ae0780,0x4a83abe190c8d09680,-0xe708ec456504f6680,0x1ca883de523223d00,-0x20cba220dadb7300,0x1217e354a447e80,-0x36dcf416b0c80,0x19f220f0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 9 36 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 36 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 22 indices rho q8 m8 8 49392000 12=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 22 indices rho q8 m8 8 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x1e8d64f660,-0x1df25f438,0x1bda8840,-0x183e058,0x135940,-0xdba8,0x838,-0x3c,0x1]
def r9 : List ℤ := raw_ints% [-0x9161bd8ec52bc000,-0xafb5f5f6baa68800,-0x5b9bf4dacd197600,-0x1af0ceb265b01580,-0x4e4cd8db5ee5060,-0x90200b351ad7a0,-0xa44dd899d0c28,-0x6a3b32a062c0,-0x1de0c658dd8]
def m9 : List ℤ := raw_ints% [0x0,-0x305bfe69c573000000,0x1f5b8724e3813d11800,-0x944465856fbd60d9200,0x1a676b40ef497794ba00,-0x3281258fbb5c98ee6880,0x445c9fc327a2ff634e80,-0x433d4f94679f8a89ee00,0x308fee2c5d2ee84be800,-0x19b550934cfef345d100,0x9d850e09e39756b0d00,-0x2a829d14d9a88281600,0x7be2ebdee428881a00,-0xe3839d866a025e280,0xebbb694acaa6e880,-0x72385c02a198e00,0x123a9e06b82800,-0x6dc30340000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 9 38 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 38 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 22 indices rho q9 m9 9 49392000 12=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 22 indices rho q9 m9 9 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x1de0c658dd8,0x1e8d64f660,-0x1df25f438,0x1bda8840,-0x183e058,0x135940,-0xdba8,0x838,-0x3c,0x1]
def r10 : List ℤ := raw_ints% [0x8e2c5693586f57000,0xab74c6ca027dcfe00,0x5928ce47efedc1b00,0x1a23ce3b3eb458e20,0x4bb2685b3ed29040,0x8abb53cc49e8ef8,0x9d56e615880ee0,0x6518c9478ec88,0x1c3849ef8200]
def m10 : List ℤ := raw_ints% [0x0,0x2444fecf54164000000,-0x173611db79e8883c0800,0x6c254ac60b34ddbd4600,-0x12f1244805b5f4f3b0e00,0x238df586a21e79b07c980,-0x2f18ddfb56cd62aca0380,0x2d2e3d00d4760fb72f300,-0x1fb0f6bf46d7ff1169d00,0x1034ff74b772012563a80,-0x5f455bf58e8543a81a80,0x1871d4f8f07331b75980,-0x42ea6854c82afbdb180,0x718ce661a18faf9600,-0x6a48f465398347400,0x2d1b5c9ef8f67380,-0x60cb462edf6980,0x1cfa24f00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 9 40 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 40 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 22 indices rho q10 m10 10 49392000 12=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 22 indices rho q10 m10 10 49392000 12 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_10
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<11) : intPolyRF (mz e)=rfPoly (C (49392000:ℚ))*rfX^12*(1-rfX)^9*momentRF (key size) (X^e) := by
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
#print axioms moment_source_10
end
end CatalanCore.Li2.NVMod.FamilySource.V4C13
