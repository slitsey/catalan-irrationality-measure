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
namespace CatalanCore.Li2.NVMod.FamilySource.U2C8
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,2,8,size⟩
def bases : List ℕ := [1,2]
def indices : List ℕ := [3,4,5,6,7,8]
def num : List ℤ := raw_ints% [0x0,0x4,0xc,0xd,0x6,0x1]
def den : List ℤ := raw_ints% [0x4ec0,0x5fe8,0x2f7a,0xc3f,0x1bd,0x21,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x6,-0x3c,0xc8,-0x20d,0x24c]
def rhoDenominators : List ℤ := raw_ints% [0xa,0x1,0x1,0x1,0x2,0x5]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-3) 0:ℚ)/(rhoDenominators.getD (m-3) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 2
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 3 9
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤8))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤8 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1]
def omegaDens3 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9]
def omega3 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums3 omegaDens3
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_3 : padCoefficients 9 omega3=padCoefficients 9 (omegaCoefficients 8 3) := by decide +kernel
theorem omega_spec_3 : coefficientsPoly omega3=omegaNumerator 8 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_3
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 9 omega4=padCoefficients 9 (omegaCoefficients 8 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 8 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 9 omega5=padCoefficients 9 (omegaCoefficients 8 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 8 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 9 omega6=padCoefficients 9 (omegaCoefficients 8 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 8 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 9 omega7=padCoefficients 9 (omegaCoefficients 8 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 8 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 9 omega8=padCoefficients 9 (omegaCoefficients 8 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 8 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x4,0x6,-0x4,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 6 li0=padCoefficients 6 (liCoefficients 5 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 5 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x3,0x3,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 6 li1=padCoefficients 6 (liCoefficients 5 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 5 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x1,-0x1,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 6 li2=padCoefficients 6 (liCoefficients 5 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 5 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,0x3,-0x3,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 6 li3=padCoefficients 6 (liCoefficients 5 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 5 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0xb,0xb,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 6 li4=padCoefficients 6 (liCoefficients 5 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 5 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x5,0xa,-0xa,0x5,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 5 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^5 := by
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
  | _=>[]
def liCache : ℕ→List ℚ
  | 0=>li0
  | 1=>li1
  | 2=>li2
  | 3=>li3
  | 4=>li4
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 8 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 3 9 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_3
  · exact omega_spec_4
  · exact omega_spec_5
  · exact omega_spec_6
  · exact omega_spec_7
  · exact omega_spec_8
theorem cache_li (j : ℕ) (hj : j<5) : coefficientsPoly (cache.li j)=liNumerator 5 j := by
  interval_cases j
  · exact li_spec_0
  · exact li_spec_1
  · exact li_spec_2
  · exact li_spec_3
  · exact li_spec_4
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x4,0xc,0xd,0x6,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x94609200,-0x40bfdb240,0xc44534c10,-0x15131bb930,0x1671db8e74,-0xf32367324,0x66cdc6398,-0x195ec8560,0x31bbc82c,-0x1eb96c4,0xa410,-0x5208,0x1068]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 6 14 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 14 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 14 indices rho q0 m0 0 21168000 8=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (21168000:ℚ))*rfX^8*(1-rfX)^5*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 14 indices rho q0 m0 0 21168000 8 5
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% [0x1]
def r1 : List ℤ := raw_ints% [-0x4ec0,-0x5fe8,-0x2f76,-0xc33,-0x1b0,-0x1b]
def m1 : List ℤ := raw_ints% [0x0,-0x4a3049000,0x1f14ba9540,-0x5a04b8f7f0,0x92e1b6ef30,-0x936a756f8c,0x5d1117203c,-0x2424185568,0x80004da28,-0xd7b874dc,0x67642ec]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 6 16 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 16 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 14 indices rho q1 m1 1 21168000 8=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (21168000:ℚ))*rfX^8*(1-rfX)^5*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 14 indices rho q1 m1 1 21168000 8 5
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% [-0x1b,0x1]
def r2 : List ℤ := raw_ints% [0x84e40,0x9ceb8,0x4a1f6,0x11b2f,0x22bc,0x1cb]
def m2 : List ℤ := raw_ints% [0x0,0x2518248000,-0xef976fc0c0,0x2994d4d1b90,-0x40a2f1f1750,0x3d4954986d4,-0x242314d5524,0xce41b147d8,-0x28db8ced18,0x3aca00604,-0x15a355f4]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 6 18 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 18 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 14 indices rho q2 m2 2 21168000 8=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (21168000:ℚ))*rfX^8*(1-rfX)^5*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 14 indices rho q2 m2 2 21168000 8 5
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [0x1cb,-0x1b,0x1]
def r3 : List ℤ := raw_ints% [-0x8d3240,-0xa3a6b8,-0x4b5106,-0x1152ff,-0x202b0,-0x186f]
def m3 : List ℤ := raw_ints% [0x0,-0x128c1240000,0x73d56bba540,-0x13565329b0f0,0x1cb871644330,-0x19c9d50308cc,0xe39142e4cfc,-0x4a9127311e8,0xd2ea7740a8,-0x10130e3a1c,0x480c8fac]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 6 20 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 20 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 14 indices rho q3 m3 3 21168000 8=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (21168000:ℚ))*rfX^8*(1-rfX)^5*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 14 indices rho q3 m3 3 21168000 8 5
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [-0x186f,0x1cb,-0x1b,0x1]
def r4 : List ℤ := raw_ints% [0x7842540,0x89a2358,0x3e45f2e,0xdfe64b,0x1925f4,0x1239f]
def m4 : List ℤ := raw_ints% [0x0,0x94609200000,-0x382ef48c84c0,0x90ccef373690,-0xce11ce83aa50,0xafa015130e94,-0x5ab8c90098e4,0x1b4befc0d3d8,-0x44af35d7518,0x4670f32f44,-0xeeb00b34]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 6 22 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 22 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 14 indices rho q4 m4 4 21168000 8=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (21168000:ℚ))*rfX^8*(1-rfX)^5*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 14 indices rho q4 m4 4 21168000 8 5
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1239f,-0x186f,0x1cb,-0x1b,0x1]
def r5 : List ℤ := raw_ints% [-0x59b52940,-0x65bc23d8,-0x2d7b076e,-0xa0ed8f3,-0x11b0518,-0xc718b]
def m5 : List ℤ := raw_ints% [0x0,-0x4a3049000000,0x1b5555b2fa140,-0x442c9a6f4bdf0,0x5d376c306d430,-0x4b92c2234230c,0x249bc6e61a03c,-0xa1bbeece56e8,0x168b30f481a8,-0x134cfacaddc,0x313174e6c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 6 24 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 24 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 14 indices rho q5 m5 5 21168000 8=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (21168000:ℚ))*rfX^8*(1-rfX)^5*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 14 indices rho q5 m5 5 21168000 8 5
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0xc718b,0x1239f,-0x186f,0x1cb,-0x1b,0x1]
def r6 : List ℤ := raw_ints% [0x3d3ed8240,0x44fb451b8,0x1e90a7d66,0x6ae76dc7,0xb9285ac,0x7f9dd3]
def m6 : List ℤ := raw_ints% [0x0,0x2518248000000,-0xd55bad90d68c0,0x2046f76b4eb190,-0x2a83cd43105950,0x20dbef76b59654,-0xef17718109da4,0x3c8810d0054d8,-0x77295f13d418,0x5490c391584,-0xa1893ba74]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 6 26 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 26 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 14 indices rho q6 m6 6 21168000 8=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (21168000:ℚ))*rfX^8*(1-rfX)^5*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 14 indices rho q6 m6 6 21168000 8 5
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_6
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<7) : intPolyRF (mz e)=rfPoly (C (21168000:ℚ))*rfX^8*(1-rfX)^5*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U2C8
