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
namespace CatalanCore.Li2.NVMod.FamilySource.U2C10
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,2,10,size⟩
def bases : List ℕ := [1,2]
def indices : List ℕ := [3,4,5,6,7,8,9,10]
def num : List ℤ := raw_ints% [0x0,0x4,0xc,0xd,0x6,0x1]
def den : List ℤ := raw_ints% [0x1baf80,0x278fd0,0x181ddc,0x8341c,0x1b499,0x38e0,0x48a,0x34,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x3,0x32,-0xaf,0x126,-0xc4,0x48]
def rhoDenominators : List ℤ := raw_ints% [0x1a4,0x5,0x1,0x3,0x4,0x5,0x5,0x7]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-3) 0:ℚ)/(rhoDenominators.getD (m-3) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 2
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 3 11
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤10))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤10 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
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
  change m∈Finset.Ico 3 11 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
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
def r0 : List ℤ := raw_ints% [0x0,0x4,0xc,0xd,0x6,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x1329886800,-0xca5fe09a00,0x3cd7eb1d100,-0xb02a476b540,0x155b13aa1a30,-0x1d35d9c54f70,0x1cde092fb85c,-0x14c0f5bdb984,0xac509058b6c,-0x3f02ed0ec5c,0xf7ef5b896c,-0x259b8767d4,0x2f413c4ac,-0x135a4244,0x5a708,-0x1e258,0x44e8]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 8 16 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 16 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 18 indices rho q0 m0 0 8001504000 10=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 18 indices rho q0 m0 0 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0xbf9f541000,0x79eb73e2800,-0x233ee9858900,0x61d921400cc0,-0xb55d6ae823d0,0xec1d1776af70,-0xdd032bc45da4,0x95957924c7fc,-0x4880f8346094,0x18815db61ccc,-0x57cda134cec,0xbda4a390b4,-0xcba52d10c,0x40ad3f54]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 8 17 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 17 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 18 indices rho q1 m1 1 8001504000 10=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 18 indices rho q1 m1 1 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x77c3948a000,-0x49a1e4a6d400,0x14847e0fd4500,-0x36bdf87cd9440,0x612d56835bc30,-0x78a8bdff65a90,0x6b2aa73d9ab7c,-0x4461830bdc1e4,0x1efce6457930c,-0x9aea7d8a1a94,0x1f8ef46ae474,-0x3c79e2debec,0x3721236ad4,-0xd75aa3cc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 8 18 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 18 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 18 indices rho q2 m2 2 8001504000 10=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 18 indices rho q2 m2 2 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [0x1]
def r3 : List ℤ := raw_ints% [-0x1baf80,-0x278fd0,-0x181ddc,-0x8341c,-0x1b495,-0x38d4,-0x47d,-0x2e]
def m3 : List ℤ := raw_ints% [0x0,-0x4ada3cd64000,0x2c9378c87ac00,-0xc00104e969500,0x1ed6d768b725c0,-0x348a8c0b3bd9d0,0x3e56c33568c970,-0x349fe1f0ddf564,0x1fb2e1ee37443c,-0xd70d925b5f754,0x3e1e23a65c80c,-0xb7f359c4d02c,0x137b7a69ac74,-0xef901d9d4c,0x2c970b514]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 8 20 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 20 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 18 indices rho q3 m3 3 8001504000 10=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 18 indices rho q3 m3 3 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [-0x2e,0x1]
def r4 : List ℤ := raw_ints% [0x4f98900,0x70027e0,0x42dcdb8,0x1613f2c,0x463f62,0x883ab,0x97f8,0x4db]
def m4 : List ℤ := raw_ints% [0x0,0x2ec86605e8000,-0x1b0c350b6b3c00,0x70ceb66207cd00,-0x117d4b7ee1e4a40,0x1ca7a0b3251eb30,-0x208c0d7b0cb8990,0x1a27a2be02f8cbc,-0xee3ed2c89e33a4,0x5e95798c6c414c,-0x1940852cce7754,0x43d6ffc404434,-0x654a63879f2c,0x412d661d494,-0x930acc50c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 8 22 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 22 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 18 indices rho q4 m4 4 8001504000 10=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 18 indices rho q4 m4 4 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x4db,-0x2e,0x1]
def r5 : List ℤ := raw_ints% [-0x866d2280,-0xbb1dbdf0,-0x6e18d354,-0x23a7363c,-0x6e6a3b7,-0xcde83e,-0xd8663,-0x6484]
def m5 : List ℤ := raw_ints% [0x0,-0x1d3d3fc3b10000,0x1072a687142fc00,-0x42907fad4cbd500,0x9fb5ed84b3e3dc0,-0xfc1fe60e5e524d0,0x112a03386e801e70,-0xd264dfd239fd624,0x71556df6baeb37c,-0x2a261e7872eab14,0xa65b5a47ce8c4c,-0x194bfff2a90e6c,0x2126d368f6634,-0x11be26f38f8c,0x1e2dbf1ad4]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 8 24 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 24 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 18 indices rho q5 m5 5 8001504000 10=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 18 indices rho q5 m5 5 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x6484,0x4db,-0x2e,0x1]
def r6 : List ℤ := raw_ints% [0xaded47e00,0xf022644c0,0x8bcfb9780,0x2ca7cfb1c,0x87c5aca8,0xf6e2fc9,0xfa56ea,0x6e46d]
def m6 : List ℤ := raw_ints% [0x0,0x124647da4ea0000,-0xa05db1a64459c00,0x27709ce8cda2bd00,-0x5bb5998be8f47e40,0x8bc063ee3ef3a430,-0x92394a2e80e68490,0x6af283eb06a275fc,-0x36903c5c6beb7264,0x130441a46107928c,-0x45500a5bc10b614,0x986e19cdbe79f4,-0xaea05650da56c,0x4d412ca3cb54,-0x62b862424c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 8 26 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 26 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 18 indices rho q6 m6 6 8001504000 10=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 18 indices rho q6 m6 6 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x6e46d,-0x6484,0x4db,-0x2e,0x1]
def r7 : List ℤ := raw_ints% [-0xbed117b980,-0x105ccf8fd90,-0x9735de61ec,-0x2fcd93886c,-0x8f6ab2e09,-0x1003a0ab8,-0xfdaa6f9,-0x6c0f3a]
def m7 : List ℤ := raw_ints% [0x0,-0xb6bece871240000,0x61ea5a3d9f9dfc00,-0x1775c62643d6b2500,0x34f7be3f80e97c1c0,-0x4e0d7a5bb718ee3d0,0x4e93098825f3b7370,-0x36f00e315ee644ae4,0x1a921e43c1d41cabc,-0x8ae46eecc31cfed4,0x1d32b74e3526e08c,-0x39e9e74c967e8ac,0x39c20714fc03f4,-0x1500ba453edcc,0x141ca854894]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 8 28 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 28 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 18 indices rho q7 m7 7 8001504000 10=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 18 indices rho q7 m7 7 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x6c0f3a,0x6e46d,-0x6484,0x4db,-0x2e,0x1]
def r8 : List ℤ := raw_ints% [0xbafaf8e4300,0xff4350c0ba0,0x9283b0daa48,0x2df42db106c,0x887cf0593e,0xf0b36d4b7,0xea43128c,0x61870cf]
def m8 : List ℤ := raw_ints% [0x0,0x723741146b680000,-0x3be55ab4b9840dc00,0xe01b07df693bd4d00,-0x1ec2e33ada4d1baa40,0x2be8d47aa309beb530,-0x2a984002f628b3df90,0x1c81893d1422edfb3c,-0xd14af5e115a086924,0x401b1099dea2c2bcc,-0xc6cdfa9424cd24d4,0x162cd02ea314c7b4,-0x132be57cde427ac,0x5b3a021318e14,-0x4157f7a638c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 8 30 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 30 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 18 indices rho q8 m8 8 8001504000 10=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 18 indices rho q8 m8 8 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x61870cf,-0x6c0f3a,0x6e46d,-0x6484,0x4db,-0x2e,0x1]
def r9 : List ℤ := raw_ints% [-0xa8c1a72ae880,-0xe5761ada0630,-0x830c60245944,-0x28d8ed00b85c,-0x78601e0e74b,-0xd2311fa3e2,-0xc9fb936df,-0x52b3d780]
def m9 : List ℤ := raw_ints% [0x0,-0x476288acc32100000,0x24b3f7fcf22f45bc00,-0x8645019501df61b500,0x11f562ba563044c35c0,-0x18df66eeb5f53d602d0,0x1748f3e8c9c4eea3870,-0xeef1fe3264219f33a4,0x681c352dff2ca0cdfc,-0x1de5db2883274bfe94,0x55659064aa4cde8cc,-0x88c69ceb55a732ec,0x6614b4e8bc0c1b4,-0x18b8c46d6d5c0c,0xd3a919bd654]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 8 32 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 32 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 18 indices rho q9 m9 9 8001504000 10=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 18 indices rho q9 m9 9 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x52b3d780,0x61870cf,-0x6c0f3a,0x6e46d,-0x6484,0x4db,-0x2e,0x1]
def r10 : List ℤ := raw_ints% [0x8f1aa04bc4000,0xc1f19d4d4af80,0x6e50b8b1cabd0,0x22367ef4d38bc,0x6432cb811324,0xad9b29fa8b5,0xa53330871e,0x42cce8f21]
def m10 : List ℤ := raw_ints% [0x0,0x2c9d956bf9f4a00000,-0x16871498d65fb5f9c00,0x50b62285e07a3b35d00,-0xa89503c9c3e0e1af640,0xe2e94e0b9992a5d1630,-0xcd4e1803e89d2ffca90,0x7e56dec316e3c690c7c,-0x344dd356cbae1d173e4,0xe14e60f8213518710c,-0x24ffa45fc77ecad794,0x35091ea7fd4a1d174,-0x22080ead50e9adec,0x6afb1c0ce454d4,-0x2abb08a0b0cc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 8 34 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 34 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 18 indices rho q10 m10 10 8001504000 10=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 18 indices rho q10 m10 10 8001504000 10 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_10
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<11) : intPolyRF (mz e)=rfPoly (C (8001504000:ℚ))*rfX^10*(1-rfX)^7*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U2C10
