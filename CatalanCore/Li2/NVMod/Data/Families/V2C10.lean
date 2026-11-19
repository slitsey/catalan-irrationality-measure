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
namespace CatalanCore.Li2.NVMod.FamilySource.V2C10
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,2,10,size⟩
def bases : List ℕ := [0,1]
def indices : List ℕ := [2,3,4,5,6,7,8,9]
def num : List ℤ := raw_ints% [0x0,0x0,0x1,0x2,0x1]
def den : List ℤ := raw_ints% [0x58980,0xa2090,0x7c44c,0x34694,0xd579,0x21b0,0x33a,0x2c,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x3,-0x19,0x19,-0x93,0xc4,-0x24]
def rhoDenominators : List ℤ := raw_ints% [0x4ec,0x14,0x5,0x9,0x4,0x14,0x2d,0x23]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-2) 0:ℚ)/(rhoDenominators.getD (m-2) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 2
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 2 10
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤9))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤9 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1]
def omegaDens2 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4]
def omega2 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums2 omegaDens2
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_2 : padCoefficients 10 omega2=padCoefficients 10 (omegaCoefficients 9 2) := by decide +kernel
theorem omega_spec_2 : coefficientsPoly omega2=omegaNumerator 9 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_2
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1]
def omegaDens3 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9]
def omega3 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums3 omegaDens3
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_3 : padCoefficients 10 omega3=padCoefficients 10 (omegaCoefficients 9 3) := by decide +kernel
theorem omega_spec_3 : coefficientsPoly omega3=omegaNumerator 9 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_3
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 10 omega4=padCoefficients 10 (omegaCoefficients 9 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 9 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 10 omega5=padCoefficients 10 (omegaCoefficients 9 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 9 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 10 omega6=padCoefficients 10 (omegaCoefficients 9 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 9 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 10 omega7=padCoefficients 10 (omegaCoefficients 9 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 9 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 10 omega8=padCoefficients 10 (omegaCoefficients 9 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 9 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 10 omega9=padCoefficients 10 (omegaCoefficients 9 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 9 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x5,0xa,-0xa,0x5,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 7 li0=padCoefficients 7 (liCoefficients 6 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 6 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x4,0x6,-0x4,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 7 li1=padCoefficients 7 (liCoefficients 6 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 6 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x2,0x0,0x2,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 7 li2=padCoefficients 7 (liCoefficients 6 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 6 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,0x2,-0x6,0x2,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 7 li3=padCoefficients 7 (liCoefficients 6 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 6 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0xa,0x0,-0xa,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 7 li4=padCoefficients 7 (liCoefficients 6 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 6 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x1a,0x42,0x1a,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 7 li5=padCoefficients 7 (liCoefficients 6 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 6 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x6,0xf,-0x14,0xf,-0x6,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 6 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^6 := by
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
  | _=>[]
def liCache : ℕ→List ℚ
  | 0=>li0
  | 1=>li1
  | 2=>li2
  | 3=>li3
  | 4=>li4
  | 5=>li5
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 9 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 2 10 at hb
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
theorem cache_li (j : ℕ) (hj : j<6) : coefficientsPoly (cache.li j)=liNumerator 6 j := by
  interval_cases j
  · exact li_spec_0
  · exact li_spec_1
  · exact li_spec_2
  · exact li_spec_3
  · exact li_spec_4
  · exact li_spec_5
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x1,0x2,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0xda06100,0x880df4c0,-0x266a1ce90,0x679bf2bcc,-0xb952e79cc,0xe6c995e0f,-0xcc36cc3db,0x8084eb15f,-0x388aa9813,0x10b3c9915,-0x31008039,0x4bf80f1,-0x28c47d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 8 15 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 15 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 16 indices rho q0 m0 0 222264000 9=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 16 indices rho q0 m0 0 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x2,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x7aa36900,-0x48ec9d3c0,0x138d27cb30,-0x31de253144,0x53efeac650,-0x61c62115d1,0x5051368d64,-0x2e781a5efb,0x128c81d456,-0x4e0e3e2b7,0xc5f6d6d8,-0xfb76d59,0x6096ce]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 8 16 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 16 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 16 indices rho q1 m1 1 222264000 9=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 16 indices rho q1 m1 1 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x2,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x44fbeb100,0x27377a39c0,-0xa044e12550,0x183d3493d1c,-0x26836688478,0x2a1637b3767,-0x202e294d4a6,0x11274327129,-0x6386b9c500,0x174d2e0019,-0x32eee359e,0x348804db,-0xe1fa54]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 8 17 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 17 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 16 indices rho q2 m2 2 222264000 9=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 16 indices rho q2 m2 2 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x2,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x26cdb43900,-0x152865a47c0,0x52a32f99230,-0xbe4d0afb764,0x11e43157d938,-0x126431830971,0xd1eb4224486,-0x6745a17d8a7,0x220d202bae4,-0x71761c203f,0xd4f1a4616,-0xb08ed8a5,0x20af038]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 8 18 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 18 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 16 indices rho q3 m3 3 222264000 9=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 16 indices rho q3 m3 3 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x1]
def r4 : List ℤ := raw_ints% [-0x58980,-0xa2090,-0x7c44c,-0x34694,-0xd579,-0x21b0,-0x339,-0x2a]
def m4 : List ℤ := raw_ints% [0x0,-0x15d3b560100,0xb73519e85c0,-0x2adf49c2e450,0x5e3aa142b49c,-0x86902aec3368,0x82705cf2d0d7,-0x56fee8804712,0x278eb9c35901,-0xbdd51eb2794,0x231eabdcc99,-0x3857eb08b2,0x252b4fb13,-0x4ae9bd0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 8 20 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 20 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 16 indices rho q4 m4 4 222264000 9=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 16 indices rho q4 m4 4 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x2a,0x1]
def r5 : List ℤ := raw_ints% [0xe88f00,0x1a3ce20,0x13c13e8,0x81cffc,0x1fbf46,0x4b167,0x65d4,0x3ff]
def m5 : List ℤ := raw_ints% [0x0,0xc4716060900,-0x6372a222b3c0,0x165fa7d52cb30,-0x2f109869619a4,0x3ff865e152c58,-0x3a9befaae48e1,0x249cddd9710ee,-0xf67bd04b7ba7,0x43407caf82dc,-0xb0870c6fbef,0xf0e0c009ee,-0x7d29f4745,0xaa436e0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 8 22 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 22 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 16 indices rho q5 m5 5 222264000 9=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 16 indices rho q5 m5 5 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x3ff,-0x2a,0x1]
def r6 : List ℤ := raw_ints% [-0x16207680,-0x278f9070,-0x1d659d94,-0xbdaf584,-0x2d33e8b,-0x66df0a,-0x8335f,-0x4a00]
def m6 : List ℤ := raw_ints% [0x0,-0x6e7fc6365100,0x3622dcfb851c0,-0xbbdf812b28350,0x17b3fdfab6d0dc,-0x1ebd3070ef00a8,0x1aace34b188227,-0xfa2535fece4a2,0x617b6df0f4051,-0x1830395095b24,0x382c808f1009,-0x40d68f7bde2,0x1a4aa15ac3,-0x18017d40]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 8 24 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 24 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 16 indices rho q6 m6 6 222264000 9=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 16 indices rho q6 m6 6 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x4a00,0x3ff,-0x2a,0x1]
def r7 : List ℤ := raw_ints% [0x199bf0000,0x2d7492980,0x2172e6790,0xd5012a6c,0x31da047c,0x6e9a175,0x87e4f6,0x484a1]
def m7 : List ℤ := raw_ints% [0x0,0x3e27df7e8d900,-0x1d8ccd317adfc0,0x6320f777a83430,-0xc0834e874ab464,0xeec23526b39558,-0xc4a50520fe3a91,0x6c4a09129d982e,-0x271c8ca04f5377,0x8d1f35357fb7c,-0x1212cfddde2bf,0x118b5febe56e,-0x581a005235,0x35cb3b80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 8 26 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 26 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 16 indices rho q7 m7 7 222264000 9=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 16 indices rho q7 m7 7 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x484a1,-0x4a00,0x3ff,-0x2a,0x1]
def r8 : List ℤ := raw_ints% [-0x1904617980,-0x2c27a9ba90,-0x2040007a4c,-0xcb5954b84,-0x2ef7b7aad,-0x6659eb34,-0x7aa4e05,-0x3ee6b6]
def m8 : List ℤ := raw_ints% [0x0,-0x22f66db72fa100,0x102bcbddd51ddc0,-0x3492043ff94f250,0x62754ad5501a41c,-0x750a1525d3fb928,0x5ba8ef49e5705f7,-0x2f7d81672642542,0xfe769e3382ab81,-0x341a641da48524,0x5de92c94a5139,-0x4c37ded3b202,0x1262d3c6153,-0x77d33d00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 8 28 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 28 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 16 indices rho q8 m8 8 222264000 9=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 16 indices rho q8 m8 8 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x3ee6b6,0x484a1,-0x4a00,0x3ff,-0x2a,0x1]
def r9 : List ℤ := raw_ints% [0x15c4a78c100,0x263fef30ce0,0x1bc62a01b78,0xadcb94aaec,0x27be1b2e82,0x557809873,0x649a7c08,0x3255943]
def m9 : List ℤ := raw_ints% [0x0,0x13aa9db70aca900,-0x8deeee5c7e0cbc0,0x1c036e227eea4d30,-0x32b6f3010cae7524,0x39e7ed370be139d8,-0x2b33010cad066641,0x1515722630f6a7ce,-0x68c6260a8b0f387,0x13742214801c7bc,-0x1ebc197a5b210f,0x14bc2ab6eff8e,-0x3d284b67165,0x109788e00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 8 30 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 30 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 16 indices rho q9 m9 9 222264000 9=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 16 indices rho q9 m9 9 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x3255943,-0x3ee6b6,0x484a1,-0x4a00,0x3ff,-0x2a,0x1]
def r10 : List ℤ := raw_ints% [-0x116b4dc07c80,-0x1e7fa24fd4b0,-0x160af94fbf04,-0x891b128d144,-0x1f1c45744bf,-0x423c13d28e,-0x4cf0169bb,-0x25d0db7c]
def m10 : List ℤ := raw_ints% [0x0,-0xb0ff8b6f611f100,0x4e08c7dc06e729c0,-0xefec27b3c8fd3150,0x1a4c8d34faf477f5c,-0x1ce70729ae5a3fea8,0x1493361ee7944fac7,-0x9783dc429f6a7222,0x2ba548364b0d9931,-0x75631ee754876e4,0xa1f492e4f85969,-0x5a52f3ff9dfe2,0xcaa25b5e363,-0x249465400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 8 32 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 32 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 16 indices rho q10 m10 10 222264000 9=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 16 indices rho q10 m10 10 222264000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_10
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<11) : intPolyRF (mz e)=rfPoly (C (222264000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V2C10
