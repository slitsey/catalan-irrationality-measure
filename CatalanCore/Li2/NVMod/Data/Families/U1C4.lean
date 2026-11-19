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
namespace CatalanCore.Li2.NVMod.FamilySource.U1C4
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,1,4,size⟩
def bases : List ℕ := [1]
def indices : List ℕ := [2,3,4]
def num : List ℤ := raw_ints% [0x0,0x1,0x2,0x1]
def den : List ℤ := raw_ints% [0x18,0x1a,0x9,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0xc,-0x12]
def rhoDenominators : List ℤ := raw_ints% [0x1,0x1,0x1]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-2) 0:ℚ)/(rhoDenominators.getD (m-2) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 1
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 2 5
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤4))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤4 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1]
def omegaDens2 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4]
def omega2 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums2 omegaDens2
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_2 : padCoefficients 5 omega2=padCoefficients 5 (omegaCoefficients 4 2) := by decide +kernel
theorem omega_spec_2 : coefficientsPoly omega2=omegaNumerator 4 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_2
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums3 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1]
def omegaDens3 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9]
def omega3 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums3 omegaDens3
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_3 : padCoefficients 5 omega3=padCoefficients 5 (omegaCoefficients 4 3) := by decide +kernel
theorem omega_spec_3 : coefficientsPoly omega3=omegaNumerator 4 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_3
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums4 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 5 omega4=padCoefficients 5 (omegaCoefficients 4 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 4 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 3 li0=padCoefficients 3 (liCoefficients 2 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 2 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 3 li1=padCoefficients 3 (liCoefficients 2 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 2 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x2,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 2 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^2 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
  | 2=>omega2
  | 3=>omega3
  | 4=>omega4
  | _=>[]
def liCache : ℕ→List ℚ
  | 0=>li0
  | 1=>li1
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 4 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 2 5 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_2
  · exact omega_spec_3
  · exact omega_spec_4
theorem cache_li (j : ℕ) (hj : j<2) : coefficientsPoly (cache.li j)=liNumerator 2 j := by
  interval_cases j
  · exact li_spec_0
  · exact li_spec_1
def q0 : List ℤ := raw_ints% [0x1]
def r0 : List ℤ := raw_ints% [-0x18,-0x19,-0x7]
def m0 : List ℤ := raw_ints% [0x0,-0x1440,0x30f0,-0x2520,0x864,0x18,-0xc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 3 10 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 10 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 7 indices rho q0 m0 0 288 4=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (288:ℚ))*rfX^4*(1-rfX)^2*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 7 indices rho q0 m0 0 288 4 2
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% [-0x7,0x1]
def r1 : List ℤ := raw_ints% [0xa8,0x9e,0x26]
def m1 : List ℤ := raw_ints% [0x0,0x5100,-0xb640,0x7aa0,-0x1560]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 3 12 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 12 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 7 indices rho q1 m1 1 288 4=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (288:ℚ))*rfX^4*(1-rfX)^2*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 7 indices rho q1 m1 1 288 4 2
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% [0x26,-0x7,0x1]
def r2 : List ℤ := raw_ints% [-0x390,-0x334,-0xb8]
def m2 : List ℤ := raw_ints% [0x0,-0x14400,0x2b080,-0x19f20,0x34e0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 3 14 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 14 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 7 indices rho q2 m2 2 288 4=true := by
  -- kcost: 3 s estimated; full cached cleared moment equality
  decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (288:ℚ))*rfX^4*(1-rfX)^2*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 7 indices rho q2 m2 2 288 4 2
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_2
def moments : List (List ℤ) := [m0,m1,m2]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<3) : intPolyRF (mz e)=rfPoly (C (288:ℚ))*rfX^4*(1-rfX)^2*momentRF (key size) (X^e) := by
  interval_cases e
  · exact moment_source_0 size
  · exact moment_source_1 size
  · exact moment_source_2 size
#print axioms moment_source_2
end
end CatalanCore.Li2.NVMod.FamilySource.U1C4
