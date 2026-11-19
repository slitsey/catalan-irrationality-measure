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
namespace CatalanCore.Li2.NVMod.FamilySource.V3C11
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,3,11,size⟩
def bases : List ℕ := [0,1,2]
def indices : List ℕ := [3,4,5,6,7,8,9,10]
def num : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def den : List ℤ := raw_ints% [0x1baf80,0x278fd0,0x181ddc,0x8341c,0x1b499,0x38e0,0x48a,0x34,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x4,0xf,-0x64,0x4c9,-0x930,0x6e4,-0x2d0]
def rhoDenominators : List ℤ := raw_ints% [0x8c,0x5,0x1,0x1,0x4,0x5,0x5,0x7]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-3) 0:ℚ)/(rhoDenominators.getD (m-3) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 3
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 3 11
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
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x7,0x15,-0x23,0x23,-0x15,0x7,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 9 li0=padCoefficients 9 (liCoefficients 8 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 8 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x6,0xf,-0x14,0xf,-0x6,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 9 li1=padCoefficients 9 (liCoefficients 8 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 8 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x4,0x5,0x0,-0x5,0x4,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 9 li2=padCoefficients 9 (liCoefficients 8 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 8 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,0x0,-0x9,0x10,-0x9,0x0,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 9 li3=padCoefficients 9 (liCoefficients 8 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 8 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x8,-0x13,0x0,0x13,-0x8,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 9 li4=padCoefficients 9 (liCoefficients 8 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 8 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x18,0xf,-0x50,0xf,0x18,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 9 li5=padCoefficients 9 (liCoefficients 8 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 8 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x38,0xf5,0x0,-0xf5,-0x38,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 9 li6=padCoefficients 9 (liCoefficients 8 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 8 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x78,0x4a7,0x970,0x4a7,0x78,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 9 li7=padCoefficients 9 (liCoefficients 8 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 8 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x8,0x1c,-0x38,0x46,-0x38,0x1c,-0x8,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 8 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^8 := by
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
  | 7=>li7
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
theorem cache_li (j : ℕ) (hj : j<8) : coefficientsPoly (cache.li j)=liNumerator 8 j := by
  interval_cases j
  · exact li_spec_0
  · exact li_spec_1
  · exact li_spec_2
  · exact li_spec_3
  · exact li_spec_4
  · exact li_spec_5
  · exact li_spec_6
  · exact li_spec_7
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x9767c400,0x69cb62e00,-0x21de855840,0x69291ea270,-0xdc9ce084e4,0x149dc0e83d0,-0x1692f9d6ab5,0x124d11a00e8,-0xaf7a0762e4,0x4ca630ebd8,-0x17b2bd760e,0x4ebd90ee8,-0x9fe5e570,0xa419498,-0x331a45]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 8 17 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 17 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 19 indices rho q0 m0 0 24696000 10=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 19 indices rho q0 m0 0 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x5ea0da800,-0x4017cbcd00,0x13d8f9f5240,-0x3b76e268d50,0x7808ef6875c,-0xac1e1686eb0,0xb402aece393,-0x8ab447567d8,0x4e837c4ce7c,-0x202269f82e8,0x935679a522,-0x1bebe8c498,0x32818beb0,-0x2c394728,0xaa2803]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 8 18 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 18 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 19 indices rho q1 m1 1 24696000 10=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 19 indices rho q1 m1 1 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% [0x1]
def r2 : List ℤ := raw_ints% [-0x1baf80,-0x278fd0,-0x181ddc,-0x8341c,-0x1b495,-0x38d4,-0x47d,-0x2e]
def m2 : List ℤ := raw_ints% [0x0,-0x3b24889000,0x26eac140b00,-0xbaed6ccbc40,0x21d9358107b0,-0x41e17dfccca4,0x5ac4fc3fb7d0,-0x5ad5d7d26425,0x42a035a075e8,-0x23aa7435aba4,0xdaffc589458,-0x3a2a26ebfae,0xa0bcb44aa8,-0x102201ff70,0xbf7c7d18,-0x233b4b5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 8 20 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 20 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 19 indices rho q2 m2 2 24696000 10=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 19 indices rho q2 m2 2 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [-0x2e,0x1]
def r3 : List ℤ := raw_ints% [0x4f98900,0x70027e0,0x42dcdb8,0x1613f2c,0x463f62,0x883ab,0x97f8,0x4db]
def m3 : List ℤ := raw_ints% [0x0,0x24f6d55a000,-0x17ae67d6bf00,0x6e80ba044e40,-0x1363b998804d0,0x2475aad231c9c,-0x305b66dbcee30,0x2e61baa52f2a3,-0x206e4576f4098,0x106f9ea23967c,-0x5eaf6749a9a8,0x174d660d7a42,-0x3a9a961cd58,0x53402dc1f0,-0x33f3b4de8,0x742e753]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 8 22 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 22 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 19 indices rho q3 m3 3 24696000 10=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 19 indices rho q3 m3 3 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x4db,-0x2e,0x1]
def r4 : List ℤ := raw_ints% [-0x866d2280,-0xbb1dbdf0,-0x6e18d354,-0x23a7363c,-0x6e6a3b7,-0xcde83e,-0xd8663,-0x6484]
def m4 : List ℤ := raw_ints% [0x0,-0x171a45584000,0xe70935e44f00,-0x419708101a040,0xb2c90743f3db0,-0x145669434fe964,0x1a032a598b5fd0,-0x17f39bd1d56e95,0xffc8ee72889e8,-0x7ad9b7a6db864,0x29849af419258,-0x976e1b0b6e4e,0x159ff11d68a8,-0x1b11f1a7a70,0xe1cb4b318,-0x17d84b25]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 8 24 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 24 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 19 indices rho q4 m4 4 24696000 10=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 19 indices rho q4 m4 4 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x6484,0x4db,-0x2e,0x1]
def r5 : List ℤ := raw_ints% [0xaded47e00,0xf022644c0,0x8bcfb9780,0x2ca7cfb1c,0x87c5aca8,0xf6e2fc9,0xfa56ea,0x6e46d]
def m5 : List ℤ := raw_ints% [0x0,0xe706b5728000,-0x8d25e7e72b700,0x2714e9e2eb6240,-0x679fc5e41e7dd0,0xb6e1f7af87d3dc,-0xe1f4af7f030b30,0xc80953d4f626b3,-0x7f9d09b3b62a98,0x3a232782367a7c,-0x1272c5c275cda8,0x3e4afffa29d62,-0x810fe6152c58,0x8dca9893d30,-0x3d58691ae8,0x4e004da3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 8 26 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 26 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 19 indices rho q5 m5 5 24696000 10=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 19 indices rho q5 m5 5 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x6e46d,-0x6484,0x4db,-0x2e,0x1]
def r6 : List ℤ := raw_ints% [-0xbed117b980,-0x105ccf8fd90,-0x9735de61ec,-0x2fcd93886c,-0x8f6ab2e09,-0x1003a0ab8,-0xfdaa6f9,-0x6c0f3a]
def m6 : List ℤ := raw_ints% [0x0,-0x9064316790000,0x5663c6703fcf00,-0x175f25c2765f440,0x3c632c8f9e9e2b0,-0x6785b4a09163e24,0x7bc1327b26c14d0,-0x697db3ee3cb8e05,0x4066da6f8227ce8,-0x1bda62ebe527724,0x84cfeba3881c58,-0x19ee1783f237ee,0x309c77e50e6a8,-0x2eac4e010970,0x10a82b66618,-0xfe413395]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 8 28 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 28 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 19 indices rho q6 m6 6 24696000 10=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 19 indices rho q6 m6 6 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x6c0f3a,0x6e46d,-0x6484,0x4db,-0x2e,0x1]
def r7 : List ℤ := raw_ints% [0xbafaf8e4300,0xff4350c0ba0,0x9283b0daa48,0x2df42db106c,0x887cf0593e,0xf0b36d4b7,0xea43128c,0x61870cf]
def m7 : List ℤ := raw_ints% [0x0,0x5a3e9ee0ba0000,-0x34f7281e0680700,0xe06570a79d09640,-0x235f454fa8333cd0,0x3affc6e19270df1c,-0x445958e1a873b630,0x382da87e739769c3,-0x20dbd43b5ffd9998,0xd804c2bff6b9e7c,-0x3c780cd962b6fa8,0xae99e8e5c0b282,-0x1277bf9ff42058,0xf6deca382a70,-0x48482ddc3e8,0x33a128cf3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 8 30 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 30 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 19 indices rho q7 m7 7 24696000 10=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 19 indices rho q7 m7 7 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x61870cf,-0x6c0f3a,0x6e46d,-0x6484,0x4db,-0x2e,0x1]
def r8 : List ℤ := raw_ints% [-0xa8c1a72ae880,-0xe5761ada0630,-0x830c60245944,-0x28d8ed00b85c,-0x78601e0e74b,-0xd2311fa3e2,-0xc9fb936df,-0x52b3d780]
def m8 : List ℤ := raw_ints% [0x0,-0x3867234c7440000,0x20866be03149bf00,-0x8716e4cbd0a34840,0x14d1ef454108153b0,-0x21d789368e56866e4,0x260cec1f35834bdd0,-0x1e32a106458d75675,0x10f0e617b90d587e8,-0x69e2069686947be4,0x1bd7131b7fd6fe58,-0x4a3a73843eefa8e,0x711c5efe5348a8,-0x51e098a402470,0x1392f5b9b518,-0xa73ceb405]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 8 32 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 32 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 19 indices rho q8 m8 8 24696000 10=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 19 indices rho q8 m8 8 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x52b3d780,0x61870cf,-0x6c0f3a,0x6e46d,-0x6484,0x4db,-0x2e,0x1]
def r9 : List ℤ := raw_ints% [0x8f1aa04bc4000,0xc1f19d4d4af80,0x6e50b8b1cabd0,0x22367ef4d38bc,0x6432cb811324,0xad9b29fa8b5,0xa53330871e,0x42cce8f21]
def m9 : List ℤ := raw_ints% [0x0,0x2340760fc8a80000,-0x1400bbffac3e6b700,0x519257cc6a8c98a40,-0xc4f901d37861463d0,0x1387d17927615c065c,-0x155811ae97cfcb5930,0x1060a3e3e6b10903d3,-0x8d2679c2478fb7098,0x3473ee2495ee2b27c,-0xcf40ce7e590c8da8,0x1fda3ddbdfdcc7a2,-0x2b95d36a8698458,0x1b3821043d79b0,-0x54a8f5cb78e8,0x21c32fe743]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 8 34 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 34 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 19 indices rho q9 m9 9 24696000 10=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 19 indices rho q9 m9 9 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x42cce8f21,-0x52b3d780,0x61870cf,-0x6c0f3a,0x6e46d,-0x6484,0x4db,-0x2e,0x1]
def r10 : List ℤ := raw_ints% [-0x739680b39a1f80,-0x9c3a39931279d0,-0x5890ed7dfd0ddc,-0x1b5af7c995afcc,-0x4fb66a3ea85fd,-0x8941988b61bc,-0x819aef60315,-0x33e6c48b96]
def m10 : List ℤ := raw_ints% [0x0,-0x160849c9dd6900000,0xc519d52cb36326f00,-0x316524adbf2d8ddc40,0x74f85e4843eb81e4b0,-0xb5623bde2be13613a4,0xc0f25a451ee25d16d0,-0x8f53e4decd2b28a7e5,0x4a3513de2f7f726ee8,-0x1a3fa56397994496a4,0x61644565193752c58,-0xdc9302f1b52f802e,0x10e3eef3072856a8,-0x9101e2f1525b70,0x16d74cedcd018,-0x6cc5d70275]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 8 36 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 36 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 19 indices rho q10 m10 10 24696000 10=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 19 indices rho q10 m10 10 24696000 10 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_10
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<11) : intPolyRF (mz e)=rfPoly (C (24696000:ℚ))*rfX^10*(1-rfX)^8*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V3C11
