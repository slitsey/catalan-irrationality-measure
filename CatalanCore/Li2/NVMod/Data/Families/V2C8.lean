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
namespace CatalanCore.Li2.NVMod.FamilySource.V2C8
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,2,8,size⟩
def bases : List ℕ := [0,1]
def indices : List ℕ := [2,3,4,5,6,7]
def num : List ℤ := raw_ints% [0x0,0x0,0x1,0x2,0x1]
def den : List ℤ := raw_ints% [0x13b0,0x1f5c,0x13f0,0x681,0x127,0x1b,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x3,0xc,-0x64,0x4b,-0x93]
def rhoDenominators : List ℤ := raw_ints% [0x1e,0x2,0x1,0x3,0x2,0xa]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-2) 0:ℚ)/(rhoDenominators.getD (m-2) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 2
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 2 8
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤7))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤7 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1]
def omegaDens2 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4]
def omega2 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums2 omegaDens2
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_2 : padCoefficients 8 omega2=padCoefficients 8 (omegaCoefficients 7 2) := by decide +kernel
theorem omega_spec_2 : coefficientsPoly omega2=omegaNumerator 7 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_2
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1]
def omegaDens3 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9]
def omega3 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums3 omegaDens3
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_3 : padCoefficients 8 omega3=padCoefficients 8 (omegaCoefficients 7 3) := by decide +kernel
theorem omega_spec_3 : coefficientsPoly omega3=omegaNumerator 7 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_3
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 8 omega4=padCoefficients 8 (omegaCoefficients 7 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 7 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 8 omega5=padCoefficients 8 (omegaCoefficients 7 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 7 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 8 omega6=padCoefficients 8 (omegaCoefficients 7 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 7 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 8 omega7=padCoefficients 8 (omegaCoefficients 7 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 7 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x3,0x3,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 5 li0=padCoefficients 5 (liCoefficients 4 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 4 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x2,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 5 li1=padCoefficients 5 (liCoefficients 4 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 4 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,0x0,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 5 li2=padCoefficients 5 (liCoefficients 4 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 4 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,0x4,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 5 li3=padCoefficients 5 (liCoefficients 4 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 4 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x4,0x6,-0x4,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 4 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^4 := by
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
  | _=>[]
def liCache : ℕ→List ℚ
  | 0=>li0
  | 1=>li1
  | 2=>li2
  | 3=>li3
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 7 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 2 8 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_2
  · exact omega_spec_3
  · exact omega_spec_4
  · exact omega_spec_5
  · exact omega_spec_6
  · exact omega_spec_7
theorem cache_li (j : ℕ) (hj : j<4) : coefficientsPoly (cache.li j)=liNumerator 4 j := by
  interval_cases j
  · exact li_spec_0
  · exact li_spec_1
  · exact li_spec_2
  · exact li_spec_3
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x1,0x2,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x183990,0x98a42c,-0x19a7d8c,0x26370cf,-0x2228d7f,0x127c252,-0x5c2eba,0xe5903,-0xbcfb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 6 13 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 13 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 12 indices rho q0 m0 0 108000 7=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (108000:ℚ))*rfX^7*(1-rfX)^4*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 12 indices rho q0 m0 0 108000 7 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x2,0x1]
def m1 : List ℤ := raw_ints% [0x0,0xa992f0,-0x3eeb0e4,0x9e3d3a8,-0xda4ea09,0xb25e2d6,-0x568e572,0x1778d48,-0x301a99,0x1c442]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 6 14 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 14 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 12 indices rho q1 m1 1 108000 7=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (108000:ℚ))*rfX^7*(1-rfX)^4*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 12 indices rho q1 m1 1 108000 7 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% [0x1]
def r2 : List ℤ := raw_ints% [-0x13b0,-0x1f5c,-0x13f0,-0x681,-0x126,-0x19]
def m2 : List ℤ := raw_ints% [0x0,-0x4a30490,0x1a140c5c,-0x3da70390,0x4f22043f,-0x3b4d7008,0x19d92bd6,-0x6165c24,0xa2c307,-0x42b2c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 6 16 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 16 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 12 indices rho q2 m2 2 108000 7=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (108000:ℚ))*rfX^7*(1-rfX)^4*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 12 indices rho q2 m2 2 108000 7 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [-0x19,0x1]
def r3 : List ℤ := raw_ints% [0x1ec30,0x2fc4c,0x1d314,0x8ea9,0x164e,0x17d]
def m3 : List ℤ := raw_ints% [0x0,0x20751ff0,-0xaddb9b44,0x1843fc5c0,-0x1d1925d79,0x140fbdd8c,-0x7dca5eca,0x19a739e4,-0x2295d61,0x9b7c8]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 6 18 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 18 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 12 indices rho q3 m3 3 108000 7=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (108000:ℚ))*rfX^7*(1-rfX)^4*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 12 indices rho q3 m3 3 108000 7 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x17d,-0x19,0x1]
def r4 : List ℤ := raw_ints% [-0x1d4cf0,-0x2cbfbc,-0x1aafe4,-0x7dae9,-0x12862,-0x11e1]
def m4 : List ℤ := raw_ints% [0x0,-0xe333df90,0x48cdcdb5c,-0x9a4910a20,0xad8802b8f,-0x6e5c6108c,0x26e65c466,-0x6d7d44ac,0x75bde47,-0x166ab0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 6 20 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 20 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 12 indices rho q4 m4 4 108000 7=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (108000:ℚ))*rfX^7*(1-rfX)^4*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 12 indices rho q4 m4 4 108000 7 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x11e1,0x17d,-0x19,0x1]
def r5 : List ℤ := raw_ints% [0x15ffdb0,0x2135eec,0x137b634,0x59987d,0xcbf5e,0xba59]
def m5 : List ℤ := raw_ints% [0x0,0x6366b1cf0,-0x1ea12faa84,0x3dde8bfb20,-0x4183530a29,0x2686486364,-0xc35f1952a,0x1d8079514,-0x190602d1,0x333c20]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 6 22 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 22 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 12 indices rho q5 m5 5 108000 7=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (108000:ℚ))*rfX^7*(1-rfX)^4*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 12 indices rho q5 m5 5 108000 7 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0xba59,-0x11e1,0x17d,-0x19,0x1]
def r6 : List ℤ := raw_ints% [-0xe54b830,-0x1573c14c,-0xc6fef84,-0x38446a5,-0x7d2412,-0x6e805]
def m6 : List ℤ := raw_ints% [0x0,-0x2b7cedca90,0xcf132fab9c,-0x1905988a460,0x1908aab6f5f,-0xda406b70dc,0x3e274783a6,-0x8027f9d0c,0x54da91f7,-0x7426c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 6 24 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 24 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 12 indices rho q6 m6 6 108000 7=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (108000:ℚ))*rfX^7*(1-rfX)^4*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 12 indices rho q6 m6 6 108000 7 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_6
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<7) : intPolyRF (mz e)=rfPoly (C (108000:ℚ))*rfX^7*(1-rfX)^4*momentRF (key size) (X^e) := by
  interval_cases e
  · exact moment_source_0 size
  · exact moment_source_1 size
  · exact moment_source_2 size
  · exact moment_source_3 size
  · exact moment_source_4 size
  · exact moment_source_5 size
  · exact moment_source_6 size
#print axioms moment_source_6
end
end CatalanCore.Li2.NVMod.FamilySource.V2C8
