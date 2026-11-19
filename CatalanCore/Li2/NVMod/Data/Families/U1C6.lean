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
namespace CatalanCore.Li2.NVMod.FamilySource.U1C6
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,1,6,size⟩
def bases : List ℕ := [1]
def indices : List ℕ := [2,3,4,5,6]
def num : List ℤ := raw_ints% [0x0,0x1,0x2,0x1]
def den : List ℤ := raw_ints% [0x2d0,0x414,0x244,0x9b,0x14,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x2,-0x9,0x28,-0x19]
def rhoDenominators : List ℤ := raw_ints% [0xc,0x1,0x1,0x3,0x4]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-2) 0:ℚ)/(rhoDenominators.getD (m-2) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 1
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 2 7
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤6))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤6 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1]
def omegaDens2 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4]
def omega2 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums2 omegaDens2
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_2 : padCoefficients 7 omega2=padCoefficients 7 (omegaCoefficients 6 2) := by decide +kernel
theorem omega_spec_2 : coefficientsPoly omega2=omegaNumerator 6 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_2
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1]
def omegaDens3 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9]
def omega3 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums3 omegaDens3
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_3 : padCoefficients 7 omega3=padCoefficients 7 (omegaCoefficients 6 3) := by decide +kernel
theorem omega_spec_3 : coefficientsPoly omega3=omegaNumerator 6 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_3
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 7 omega4=padCoefficients 7 (omegaCoefficients 6 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 6 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 7 omega5=padCoefficients 7 (omegaCoefficients 6 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 6 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 7 omega6=padCoefficients 7 (omegaCoefficients 6 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 6 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
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
  | _=>[]
def liCache : ℕ→List ℚ
  | 0=>li0
  | 1=>li1
  | 2=>li2
  | 3=>li3
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 6 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 2 7 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_2
  · exact omega_spec_3
  · exact omega_spec_4
  · exact omega_spec_5
  · exact omega_spec_6
theorem cache_li (j : ℕ) (hj : j<4) : coefficientsPoly (cache.li j)=liNumerator 4 j := by
  interval_cases j
  · exact li_spec_0
  · exact li_spec_1
  · exact li_spec_2
  · exact li_spec_3
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x1,0x2,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x83d60,0x307a28,-0x77e5c0,0xa0b8ba,-0x7d1068,0x37b66c,-0xcd028,0x118fa,0x1e0,-0x78]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 5 11 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 11 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 11 indices rho q0 m0 0 86400 6=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (86400:ℚ))*rfX^6*(1-rfX)^4*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 11 indices rho q0 m0 0 86400 6 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x1,0x2,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x317040,-0x11148f0,0x275bc80,-0x309961c,0x2245570,-0xd7c7d8,0x29dd30,-0x2b87c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 5 12 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 12 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 11 indices rho q1 m1 1 86400 6=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (86400:ℚ))*rfX^6*(1-rfX)^4*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 11 indices rho q1 m1 1 86400 6 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% [0x1]
def r2 : List ℤ := raw_ints% [-0x2d0,-0x414,-0x244,-0x9a,-0x12]
def m2 : List ℤ := raw_ints% [0x0,-0x128a180,0x60fd1a0,-0xd19e800,0xefc9ca8,-0x99daea0,0x3586710,-0x8b2c20,0x68ee8]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 5 14 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 14 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 11 indices rho q2 m2 2 86400 6=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (86400:ℚ))*rfX^6*(1-rfX)^4*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 11 indices rho q2 m2 2 86400 6 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [-0x12,0x1]
def r3 : List ℤ := raw_ints% [0x32a0,0x4698,0x24b4,0x8a2,0xce]
def m3 : List ℤ := raw_ints% [0x0,0x6f3c900,-0x22a775c0,0x46afcd00,-0x4b4e8ef0,0x2c1e4340,-0xd9108e0,0x1d4c640,-0xf91f0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 5 16 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 16 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 11 indices rho q3 m3 3 86400 6=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (86400:ℚ))*rfX^6*(1-rfX)^4*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 11 indices rho q3 m3 3 86400 6 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0xce,-0x12,0x1]
def r4 : List ℤ := raw_ints% [-0x24360,-0x31578,-0x18c20,-0x5806,-0x776]
def m4 : List ℤ := raw_ints% [0x0,-0x29b6b600,0xc7577e80,-0x182004f00,0x180e3fea0,-0xce824280,0x38110d40,-0x637bf80,0x247ca0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 5 18 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 18 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 11 indices rho q4 m4 4 86400 6=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (86400:ℚ))*rfX^6*(1-rfX)^4*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 11 indices rho q4 m4 4 86400 6 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x776,0xce,-0x12,0x1]
def r5 : List ℤ := raw_ints% [0x14fbe0,0x1c29d8,0xdd1e0,0x2f852,0x3d32]
def m5 : List ℤ := raw_ints% [0x0,0xfa484400,-0x48122a300,0x853581f00,-0x7ce81a6c0,0x3d8abd480,-0xeb843c80,0x1530da80,-0x548bc0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 5 20 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 20 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 11 indices rho q5 m5 5 86400 6=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (86400:ℚ))*rfX^6*(1-rfX)^4*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 11 indices rho q5 m5 5 86400 6 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x3d32,-0x776,0xce,-0x12,0x1]
def r6 : List ℤ := raw_ints% [-0xac1ca0,-0xe49408,-0x6e7b70,-0x173b66,-0x1cf96]
def m6 : List ℤ := raw_ints% [0x0,-0x5ddb19800,0x1a303c2e00,-0x2e707b1300,0x2922d90580,-0x12a842da00,0x3eaf79200,-0x483f9b00,0xc1fe80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 5 22 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 22 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 11 indices rho q6 m6 6 86400 6=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (86400:ℚ))*rfX^6*(1-rfX)^4*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 11 indices rho q6 m6 6 86400 6 4
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_6
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<7) : intPolyRF (mz e)=rfPoly (C (86400:ℚ))*rfX^6*(1-rfX)^4*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U1C6
