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
namespace CatalanCore.Li2.NVMod.FamilySource.V2C11
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,2,11,size⟩
def bases : List ℕ := [0,1]
def indices : List ℕ := [2,3,4,5,6,7,8,9,10]
def num : List ℤ := raw_ints% [0x0,0x0,0x1,0x2,0x1]
def den : List ℤ := raw_ints% [0x375f00,0x6acf20,0x57cb88,0x288614,0xb9d4e,0x22659,0x41f4,0x4f2,0x36,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x5,0x19,-0x31,0x62,-0x24,0x2d]
def rhoDenominators : List ℤ := raw_ints% [0x2760,0x8c,0xa,0x9,0x10,0x14,0x2d,0x23,0xe0]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-2) 0:ℚ)/(rhoDenominators.getD (m-2) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 2
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 2 11
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤10))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤10 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1]
def omegaDens2 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4]
def omega2 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums2 omegaDens2
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_2 : padCoefficients 11 omega2=padCoefficients 11 (omegaCoefficients 10 2) := by decide +kernel
theorem omega_spec_2 : coefficientsPoly omega2=omegaNumerator 10 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_2
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1]
def omegaDens3 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9]
def omega3 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums3 omegaDens3
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_3 : padCoefficients 11 omega3=padCoefficients 11 (omegaCoefficients 10 3) := by decide +kernel
theorem omega_spec_3 : coefficientsPoly omega3=omegaNumerator 10 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_3
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 11 omega4=padCoefficients 11 (omegaCoefficients 10 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 10 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 11 omega5=padCoefficients 11 (omegaCoefficients 10 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 10 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 11 omega6=padCoefficients 11 (omegaCoefficients 10 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 10 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 11 omega7=padCoefficients 11 (omegaCoefficients 10 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 10 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 11 omega8=padCoefficients 11 (omegaCoefficients 10 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 10 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 11 omega9=padCoefficients 11 (omegaCoefficients 10 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 10 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 11 omega10=padCoefficients 11 (omegaCoefficients 10 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 10 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x6,0xf,-0x14,0xf,-0x6,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 8 li0=padCoefficients 8 (liCoefficients 7 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 7 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x5,0xa,-0xa,0x5,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 8 li1=padCoefficients 8 (liCoefficients 7 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 7 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x3,0x2,0x2,-0x3,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 8 li2=padCoefficients 8 (liCoefficients 7 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 7 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,0x1,-0x8,0x8,-0x1,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 8 li3=padCoefficients 8 (liCoefficients 7 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 7 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x9,-0xa,-0xa,0x9,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 8 li4=padCoefficients 8 (liCoefficients 7 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 7 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x19,0x28,-0x28,-0x19,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 8 li5=padCoefficients 8 (liCoefficients 7 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 7 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x39,0x12e,0x12e,0x39,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 8 li6=padCoefficients 8 (liCoefficients 7 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 7 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x7,0x15,-0x23,0x23,-0x15,0x7,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 7 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^7 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
  | 2=>omega2
  | 3=>omega3
  | 4=>omega4
  | 5=>omega5
  | 6=>omega6
  | 7=>omega7
  | 8=>omega8
  | 9=>omega9
  | 10=>omega10
  | _=>[]
def liCache : ℕ→List ℚ
  | 0=>li0
  | 1=>li1
  | 2=>li2
  | 3=>li3
  | 4=>li4
  | 5=>li5
  | 6=>li6
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 10 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 2 11 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_2
  · exact omega_spec_3
  · exact omega_spec_4
  · exact omega_spec_5
  · exact omega_spec_6
  · exact omega_spec_7
  · exact omega_spec_8
  · exact omega_spec_9
  · exact omega_spec_10
theorem cache_li (j : ℕ) (hj : j<7) : coefficientsPoly (cache.li j)=liNumerator 7 j := by
  interval_cases j
  · exact li_spec_0
  · exact li_spec_1
  · exact li_spec_2
  · exact li_spec_3
  · exact li_spec_4
  · exact li_spec_5
  · exact li_spec_6
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x1,0x2,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x552a5e40,-0x3f2ea1c30,0x158b745a90,-0x47836fadcc,0xa110dd0854,-0x103d51fa8ec,0x134c7370794,-0x111a19d2103,0xb4d733cad5,-0x581c29a52f,0x1ed9a835f9,-0x76988303d,0x11ffb1d4b,-0x176c4169,0xaac3ef]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 9 16 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 16 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 18 indices rho q0 m0 0 7112448000 10=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 18 indices rho q0 m0 0 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x2,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x353a7ae80,0x25c918f9e0,-0xc4bcc0d1a0,0x26d4c645ff8,-0x52e9c8307c8,0x7e47587e638,-0x8cf8f2b5068,0x74a4f5f0cde,-0x476f0974512,0x1fefa774596,-0xa203abf6ba,0x2297aeb8a2,-0x487ceffae,0x4d31e05a,-0x19317b6]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 9 17 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 17 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 18 indices rho q1 m1 1 7112448000 10=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 18 indices rho q1 m1 1 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x2,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x21448cd100,-0x16a868ca2c0,0x70e31e09840,-0x15417db7e1b0,0x2b24b37ebf50,-0x3e32d5500bb0,0x4164d6359ff0,-0x32a42ec21a0c,0x1ccc3bcb26d4,-0xbd535224dbc,0x3667800c1a4,-0xa5117c0474,0x12984d76ac,-0x100f23ea4,0x3ac135c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 9 18 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 18 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 18 indices rho q2 m2 2 7112448000 10=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 18 indices rho q2 m2 2 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x2,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x14cad802a00,0xd9f49a83b80,-0x411d0ba89a80,0xbb9f5dc2eee0,-0x16aebfda72ba0,0x1f07b1ee84260,-0x1ecbd21a0c380,0x165e1119382d8,-0xbd4f7d06ca68,0x4794b5d04438,-0x12a6330eed48,0x3232b5175a8,-0x4d843f5398,0x35c368c88,-0x8797718]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 9 19 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 19 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 18 indices rho q3 m3 3 7112448000 10=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 18 indices rho q3 m3 3 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x2,0x1]
def m4 : List ℤ := raw_ints% [0x0,0xcfec701a400,-0x835f2a0b3300,0x25bf7f2c5f100,-0x684a27f2216c0,0xc0b57735e81c0,-0xfabaef4208440,0xeb656f4eb4de0,-0xa0a6dfb195d90,0x4f2b91b004270,-0x1b92996d038d0,0x6834fab9e070,-0xf870a61cdf0,0x14735556c90,-0xb46e861b0,0x13609ff0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 9 20 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 20 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 18 indices rho q4 m4 4 7112448000 10=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 18 indices rho q4 m4 4 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0x375f00,-0x6acf20,-0x57cb88,-0x288614,-0xb9d4e,-0x22659,-0x41f4,-0x4f1,-0x34]
def m5 : List ℤ := raw_ints% [0x0,-0x81f3c6106800,0x4f61039afde00,-0x15fd9ddd2a9200,0x3a64058b27a180,-0x674e2d20fdf400,0x801b7c03682a00,-0x71ff54955082e0,0x493a63209aaa80,-0x21a986c58e9600,0xace1e6e522580,-0x2502a36243ec0,0x4dfe12b76200,-0x572c155c500,0x25d8a0f480,-0x2bf2c560]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 9 22 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 22 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 18 indices rho q5 m5 5 7112448000 10=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 18 indices rho q5 m5 5 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x34,0x1]
def r6 : List ℤ := raw_ints% [0xb3f4c00,0x157ab380,0x116a8880,0x7e37088,0x2336dc4,0x642cc6,0xb3f37,0xbf34,0x607]
def m6 : List ℤ := raw_ints% [0x0,0x51385bca41000,-0x3013bf801d8c00,0xcdf0f39e921c00,-0x20eba9380dc7100,0x37e2d42ccceed80,-0x42300db8ca8e480,0x37ed0a2bcb675a0,-0x21dd6443d5f6f20,0xe8960dfb404960,-0x44d5a6afd5a6a0,0xd58886e9a9a20,-0x18cc28a491860,0x1765216f8ba0,-0x7ecdd9c860,0x62f4d9c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 9 24 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 24 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 18 indices rho q6 m6 6 7112448000 10=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 18 indices rho q6 m6 6 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x607,-0x34,0x1]
def r7 : List ℤ := raw_ints% [-0x14dbd9900,-0x278871de0,-0x1fbb10d38,-0xe2d59a0c,-0x3e1db09a,-0xac1b4ab,-0x12958e6,-0x128f67,-0x8646]
def m7 : List ℤ := raw_ints% [0x0,-0x32c3395e68a000,0x1d2f5823a5d5800,-0x79153d173e0c000,0x12af4506bb41c800,-0x1e7f85da52eac180,0x228fe2c609debc80,-0x1bc6e3e3de303e60,0xfe077d5050d7e20,-0x65e9b43f0fe3f60,0x1bd01345b4513a0,-0x4e0f519efc9fa0,0x7f85c36013660,-0x64fcdb385fa0,0x1a7b626d360,-0xdd60d980]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 9 26 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 26 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 18 indices rho q7 m7 7 7112448000 10=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 18 indices rho q7 m7 7 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x8646,0x607,-0x34,0x1]
def r8 : List ℤ := raw_ints% [0x1d0addfa00,0x36b7e1c9c0,0x2b9403b950,0x1345921440,0x534ae3d48,0xe28b61bc,0x17d60c0d,0x16ead46,0x9c35d]
def m8 : List ℤ := raw_ints% [0x0,0x1fba03db0164000,-0x11c147574a8a5000,0x477f5cc95a506800,-0xaac2f9ae2c2f5200,0x10c86b1c75ece7c80,-0x123b62b46a2ea2580,0xdf57ff9db7a872a0,-0x78a6cc8bbf0c9560,0x2d453df10c510520,-0xb643c0d1bc8e5e0,0x1ce35260f2274e0,-0x295c8e62d31a20,0x1b57152acc7e0,-0x58324128b20,0x1ec610f00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 9 28 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 28 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 18 indices rho q8 m8 8 7112448000 10=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 18 indices rho q8 m8 8 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x9c35d,-0x8646,0x607,-0x34,0x1]
def r9 : List ℤ := raw_ints% [-0x21c987a8300,-0x3f5bfd4a4a0,-0x3226fd3bea8,-0x1600f8a37f4,-0x5e1f367b16,-0xfc8707c0d,-0x1a15d6fe8,-0x187215dd,-0xa08858]
def m9 : List ℤ := raw_ints% [0x0,-0x13d44268e0de8000,0xad2dfbb203730000,-0x2a6433a6af6f43800,0x6222220921cff3200,-0x94f34539f213e0f80,0x9b61ef0cc14f9ce80,-0x71809f349b9bc9660,0x3a0371c135f186ea0,-0x145ea94d5be501ae0,0x4b983838f0f2e620,-0xacef49fb97dc520,0xd8443ad87e9de0,-0x76aabb8bd6420,0x124ac6c5a4e0,-0x44162f600]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 9 30 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 30 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 18 indices rho q9 m9 9 7112448000 10=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 18 indices rho q9 m9 9 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0xa08858,0x9c35d,-0x8646,0x607,-0x34,0x1]
def r10 : List ℤ := raw_ints% [0x22b8dd80a800,0x40ddbe45b000,0x331837799220,0x1646f1d4f838,0x5e870c54adc,0xfafd85fb82,0x19932fcfd3,0x17884d348,0x96aacb3]
def m10 : List ℤ := raw_ints% [0x0,0xc64a9818c8b10000,-0x69c7699860ce8e000,0x193b6d300693db9800,-0x38b909a4ac4894d600,0x5340bf1fc5d9545080,-0x53895960f5bfcc3180,0x3a4d05b86a2469dca0,-0x1c3918b265f7529060,0x946ef3f7e3a2da220,-0x1fb7da1fb532594e0,0x4155c6e4f34c99e0,-0x471aec7bbae1720,0x20380f32b7cae0,-0x3c79fdd88420,0x95ecbdc00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 9 32 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 32 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 18 indices rho q10 m10 10 7112448000 10=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 18 indices rho q10 m10 10 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x96aacb3,-0xa08858,0x9c35d,-0x8646,0x607,-0x34,0x1]
def r11 : List ℤ := raw_ints% [-0x20969b08b6d00,-0x3cb111397ab60,-0x2f9df8a2d0018,-0x14a8157399ddc,-0x5717c4466d52,-0xe560459515f,-0x1721200121a,-0x14fe5a3d63,-0x83fb9a7a]
def m11 : List ℤ := raw_ints% [0x0,-0x7bee9f0f7d6ea0000,0x40baa2e85dbedaa000,-0xf12f2bcde227709800,0x20f7bc27cc0d944fa00,-0x2edf0d7dd4b74b50f80,0x2d4f6550c46e08a2e80,-0x1e40dbea2f98f037060,0xde240f31d8934c06a0,-0x446033ebd0f6c6eae0,0xd73790f3934b5ce20,-0x18e54f4c638e3f920,0x177d9b88b685bde0,-0x8bf56b45358420,0xc7360aee3ce0,-0x148b2c1800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 9 34 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 34 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 18 indices rho q11 m11 11 7112448000 10=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 18 indices rho q11 m11 11 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x83fb9a7a,0x96aacb3,-0xa08858,0x9c35d,-0x8646,0x607,-0x34,0x1]
def r12 : List ℤ := raw_ints% [0x1c8c088e894600,0x35078d37548840,0x29785f0d072370,0x11ea909b66ed70,0x4b267d06a4550,0xc4a4ac146318,0x13aaa9aee4e9,0x11aa041dd3a,0x6d8b85859]
def m12 : List ℤ := raw_ints% [0x0,0x4d752369ae65240000,-0x27ad86545d4a05b2000,0x909697b9d78f227d800,-0x1342e7d3e05633600600,0x1a9244bcf47182ff9880,-0x18c8eba90a54c5790980,0xfda49ff64e4c5277aa0,-0x6e70dfeba379d670660,0x1fd6300bae2f7555c20,-0x5c2af14c4115e7cae0,0x98eb8df595a3e9fe0,-0x7c9fa2ba15135920,0x25f8d43f39290e0,-0x28dde27808e20,0x2cdc91f000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 9 36 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 36 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 18 indices rho q12 m12 12 7112448000 10=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 18 indices rho q12 m12 12 7112448000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<13) : intPolyRF (mz e)=rfPoly (C (7112448000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^e) := by
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
#print axioms moment_source_12
end
end CatalanCore.Li2.NVMod.FamilySource.V2C11
