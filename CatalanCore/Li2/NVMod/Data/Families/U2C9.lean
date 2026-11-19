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
namespace CatalanCore.Li2.NVMod.FamilySource.U2C9
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,2,9,size⟩
def bases : List ℕ := [1,2]
def indices : List ℕ := [3,4,5,6,7,8,9]
def num : List ℤ := raw_ints% [0x0,0x4,0xc,0xd,0x6,0x1]
def den : List ℤ := raw_ints% [0x2c4c0,0x3ade8,0x20b32,0x9db1,0x1be4,0x2e6,0x2a,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x6,-0xf,0xc8,-0x20d,0x24c,-0xc4]
def rhoDenominators : List ℤ := raw_ints% [0x3c,0x5,0x1,0x3,0x4,0x5,0x5]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-3) 0:ℚ)/(rhoDenominators.getD (m-3) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 2
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 3 10
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤9))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤9 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
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
  change m∈Finset.Ico 3 10 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
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
def r0 : List ℤ := raw_ints% [0x0,0x4,0xc,0xd,0x6,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x537652200,0x2da4b4e980,-0xb272f6bba0,0x19a38047918,-0x26598b6d7b0,0x26fa1941306,-0x1b417956334,0xcf6f6ad4ea,-0x40990b1b00,0xc26ebc1aa,-0x12a2022bc,0x931363e,-0x2e248,0x12750,-0x3138]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 7 15 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 15 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 16 indices rho q0 m0 0 571536000 9=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (571536000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 16 indices rho q0 m0 0 571536000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x2ef28e3200,-0x18b242ccf80,0x5c920bb65e0,-0xcb37f9d6f68,0x120e25b80770,-0x1155a8201cea,0xb5c865a51cc,-0x50323c4d666,0x16d163360d8,-0x3d4f89a136,0x5087a354c,-0x1ed0b3d2]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 7 16 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 16 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 16 indices rho q1 m1 1 571536000 9=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (571536000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 16 indices rho q1 m1 1 571536000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% [0x1]
def r2 : List ℤ := raw_ints% [-0x2c4c0,-0x3ade8,-0x20b32,-0x9dad,-0x1bd8,-0x2d9,-0x24]
def m2 : List ℤ := raw_ints% [0x0,-0x1a686ffc200,0xd6714181b80,-0x304dc56da720,0x6589cd590698,-0x898305aae290,0x7cf8e0730666,-0x4ce3b159b614,0x1f7ba5ea214a,-0x82df8ba6368,0x1390adf557a,-0x15dd5e7d94,0x66dd437e]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 7 18 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 18 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 16 indices rho q2 m2 2 571536000 9=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (571536000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 16 indices rho q2 m2 2 571536000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [-0x24,0x1]
def r3 : List ℤ := raw_ints% [0x63ab00,0x81afe0,0x45e520,0x1421b2,0x34e63,0x4c80,0x30f]
def m3 : List ℤ := raw_ints% [0x0,0xedabefdd200,-0x74b628ff7780,0x1958d6c380be0,-0x332681835fee8,0x4225d13989970,-0x390412d028bca,0x20f9a4a3e338c,-0xc89cb4609d06,0x2f8da8fde958,-0x64f051c5d56,0x5f4b37b70c,-0x1558d4eb2]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 7 20 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 20 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 16 indices rho q3 m3 3 571536000 9=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (571536000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 16 indices rho q3 m3 3 571536000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x30f,-0x24,0x1]
def r4 : List ℤ := raw_ints% [-0x877c740,-0xadd3d98,-0x5be8e0e,-0x19c6b3f,-0x412caa,-0x58f17,-0x33f6]
def m4 : List ℤ := raw_ints% [0x0,-0x85b0b6ec6200,0x3fb1b122f3380,-0xd5f344961fd20,0x19f815eeb5df18,-0x2023b6f564a590,0x1a528d2831e686,-0xe541e03fbc3d4,0x50fa84460832a,-0x117e744367ee8,0x20d670eb555a,-0x1a009222754,0x468a49d1e]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 7 22 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 22 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 16 indices rho q4 m4 4 571536000 9=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (571536000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 16 indices rho q4 m4 4 571536000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x33f6,0x30f,-0x24,0x1]
def r5 : List ℤ := raw_ints% [0x8fdb5080,0xb6b68db0,0x5f547a74,0x1a433d08,0x40ccdd9,0x556e5a,0x2f745]
def m5 : List ℤ := raw_ints% [0x0,0x4b3366e4f7200,-0x22d990ad48cf80,0x71717fd33fe5e0,-0xd486345ec01668,0xfc3ff09dd41a70,-0xc4a53368db9aaa,0x64ddaeb7c738cc,-0x211a6aeafe24a6,0x6823771b8c4d8,-0xac3463c4aa76,0x7193bfc374c,-0xe81385792]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 7 24 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 24 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 16 indices rho q5 m5 5 571536000 9=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (571536000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 16 indices rho q5 m5 5 571536000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x2f745,-0x33f6,0x30f,-0x24,0x1]
def r6 : List ℤ := raw_ints% [-0x8361447c0,-0xa59bd6708,-0x55907b4ca,-0x1745dcd41,-0x3875436c,-0x48be425,-0x2722f8]
def m6 : List ℤ := raw_ints% [0x0,-0x2a4ce9e0cb0200,0x131d2fe648f4b80,-0x3c70a661c391320,0x6d78c921aeabf98,-0x7cde6aa5eec8490,0x5ccf9a082805ca6,-0x2ce7c9d36356694,0xdb18106ee0390a,-0x272472a5f21468,0x38c9770e9fb3a,-0x1efe31325614,0x2f8785cebe]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 7 26 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 26 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 16 indices rho q6 m6 6 571536000 9=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (571536000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 16 indices rho q6 m6 6 571536000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x2722f8,0x2f745,-0x33f6,0x30f,-0x24,0x1]
def r7 : List ℤ := raw_ints% [0x6c5a101a00,0x87c8ed0100,0x45a2581568,0x12c27990ae,0x2cf2d7f9f,0x38fa1764,0x1dfd88b]
def m7 : List ℤ := raw_ints% [0x0,0x17cb438e7231200,-0xa81d233f109a780,0x2058ba2481979fe0,-0x38c46a55bc89f5e8,0x3e59b93ef24a8370,-0x2c41adbcfea2fb8a,0x1437b7b5d8f9200c,-0x5ba3b67fd186e46,0xed910e6f626658,-0x12d141a71d3196,0x872ad92b178c,-0x9b2c1f9a72]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 7 28 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 28 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 16 indices rho q7 m7 7 571536000 9=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (571536000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 16 indices rho q7 m7 7 571536000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1dfd88b,-0x2722f8,0x2f745,-0x33f6,0x30f,-0x24,0x1]
def r8 : List ℤ := raw_ints% [-0x5307ac2d440,-0x67927c312f8,-0x34ce42f4326,-0xe1f139e1b3,-0x2184b9f41e,-0x29fa02343,-0x15bf6f6a]
def m8 : List ℤ := raw_ints% [0x0,-0xd625600203ba200,0x5c9b9de6b956e380,-0x1162824e4fd6e4920,0x1d9f9fd51ccaf3818,-0x1f6418d09b8776390,0x154fc08b45e14f0c6,-0x9334497ca82eb954,0x26ba83a1a0d91cea,-0x5adaee76daab5e8,0x6423bb5c21551a,-0x24c90086194d4,0x1f8e2f0dc5e]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 7 30 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 30 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 16 indices rho q8 m8 8 571536000 9=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (571536000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 16 indices rho q8 m8 8 571536000 9 6
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_8
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<9) : intPolyRF (mz e)=rfPoly (C (571536000:ℚ))*rfX^9*(1-rfX)^6*momentRF (key size) (X^e) := by
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
#print axioms moment_source_8
end
end CatalanCore.Li2.NVMod.FamilySource.U2C9
