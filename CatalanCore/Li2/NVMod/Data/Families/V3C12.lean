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
namespace CatalanCore.Li2.NVMod.FamilySource.V3C12
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,3,12,size⟩
def bases : List ℕ := [0,1,2]
def indices : List ℕ := [3,4,5,6,7,8,9,10,11]
def num : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def den : List ℤ := raw_ints% [0x1308a80,0x1cedd70,0x130d844,0x725b10,0x1af6af,0x42639,0x6ace,0x6c6,0x3f,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x4,0x5,-0x14,0x4c9,-0x310,0x372,-0x2d0,0x1545]
def rhoDenominators : List ℤ := raw_ints% [0x460,0x23,0x2,0x1,0x10,0x5,0x5,0x7,0xe0]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-3) 0:ℚ)/(rhoDenominators.getD (m-3) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 3
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 3 12
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤11))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤11 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1]
def omegaDens3 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9]
def omega3 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums3 omegaDens3
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_3 : padCoefficients 12 omega3=padCoefficients 12 (omegaCoefficients 11 3) := by decide +kernel
theorem omega_spec_3 : coefficientsPoly omega3=omegaNumerator 11 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_3
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 12 omega4=padCoefficients 12 (omegaCoefficients 11 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 11 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 12 omega5=padCoefficients 12 (omegaCoefficients 11 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 11 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 12 omega6=padCoefficients 12 (omegaCoefficients 11 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 11 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 12 omega7=padCoefficients 12 (omegaCoefficients 11 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 11 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 12 omega8=padCoefficients 12 (omegaCoefficients 11 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 11 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 12 omega9=padCoefficients 12 (omegaCoefficients 11 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 11 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 12 omega10=padCoefficients 12 (omegaCoefficients 11 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 11 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 12 omega11=padCoefficients 12 (omegaCoefficients 11 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 11 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
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
  | 11=>omega11
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 11 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 3 12 at hb
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
  · exact omega_spec_11
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x47900ba40,-0x311dbd6930,0xf6cd344990,-0x2ee9f53970c,0x603e343c294,-0x8c7109c63ac,0x95ba315b2b4,-0x75d9a917b33,0x445379346a5,-0x1cbeb5bd51f,0x8826556ec9,-0x1ada0ad98d,0x332a7d77b,-0x304e78f9,0xd500bf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 9 18 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 18 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 19 indices rho q0 m0 0 790272000 11=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 19 indices rho q0 m0 0 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x31330800c0,0x2095a2b0510,-0x9da2771e930,0x1cc5b1b9b584,-0x3880c6f2d65c,0x4ea4179e31e4,-0x4f9e1f384a3c,0x3b3193495811,-0x2033510adf37,0xc99ee4ef5b5,-0x36e0e317a43,0x9c9e42dfaf,-0x107248dea9,0xd18fe853,-0x2c3bf95]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 9 19 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 19 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 19 indices rho q1 m1 1 790272000 11=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 19 indices rho q1 m1 1 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x21d31580840,-0x15a99e2437b0,0x6519fa206510,-0x11c1266d524ac,0x2170703c333f4,-0x2c77cada73b4c,0x2ad1f80824414,-0x1e1c7cd7342db,0xf625737e223d,-0x59a54cc43467,0x166db8d03e41,-0x39ce0fafae5,0x5557ed9fe3,-0x38f4b16f1,0x9243b07]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 9 20 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 20 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 19 indices rho q2 m2 2 790272000 11=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 19 indices rho q2 m2 2 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [0x1]
def r3 : List ℤ := raw_ints% [-0x1308a80,-0x1cedd70,-0x130d844,-0x725b10,-0x1af6af,-0x42635,-0x6ac2,-0x6b9,-0x39]
def m3 : List ℤ := raw_ints% [0x0,-0x17411ec85ac0,0xe6e53a7c6490,-0x411accdf4f7b0,0xb056083006b64,-0x13f190616a6d7c,0x1961e87e8ec5c4,-0x17482df542b95c,0xf810769fd8e49,-0x77223ac530cbf,0x286440fd137cd,-0x948da27d2a6b,0x1592ab665477,-0x1be300efd21,0xf7f20effb,-0x1e17f2ad]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 9 22 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 22 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 19 indices rho q3 m3 3 790272000 11=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 19 indices rho q3 m3 3 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [-0x39,0x1]
def r4 : List ℤ := raw_ints% [0x43ced680,0x65dec370,0x421149b4,0x18456e4c,0x58e91e7,0xd18c02,0x13a1a9,0x11754,0x74e]
def m4 : List ℤ := raw_ints% [0x0,0xffcc529be640,-0x9a1ebd8a45230,0x2a168d8962c490,-0x6e16edb09eb54c,0xbfbdf8eef80254,-0xe9ece30c599dec,0xccab4636091274,-0x81368f975bad43,0x3a5fbf7032e915,-0x126d7860e9396f,0x3e39d5f3fc9f9,-0x821937d7617d,0x92b09f9750b,-0x43775d7d29,0x62aa830f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 9 24 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 24 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 19 indices rho q4 m4 4 790272000 11=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 19 indices rho q4 m4 4 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x74e,-0x39,0x1]
def r5 : List ℤ := raw_ints% [-0x8b093b300,-0xcf146b1a0,-0x84cecfd48,-0x30143e52c,-0xacb08406,-0x18c0a277,-0x23aa0c2,-0x1dd8ab,-0xb4de]
def m5 : List ℤ := raw_ints% [0x0,-0xafdc78cb2e4c0,0x6711d9a4078810,-0x1b4fa36d5bc9230,0x451cc04881fa244,-0x740c7d5cb728b9c,0x87ec27597122aa4,-0x719620511bf6f7c,0x440deb086e6fac1,-0x1cf04d7e7283e07,0x88191ec7563125,-0x1a599a923aa953,0x3177a8a566aff,-0x307625f5b7d9,0x12585776263,-0x1424a3d05]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 9 26 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 26 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 19 indices rho q5 m5 5 790272000 11=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 19 indices rho q5 m5 5 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0xb4de,0x74e,-0x39,0x1]
def r6 : List ℤ := raw_ints% [0xd7297a1b00,0x13e54831420,0xca6f24a958,0x487e453a98,0x100b911296,0x241c8b568,0x32b4d42d,0x28e76f2,0xea9f7]
def m6 : List ℤ := raw_ints% [0x0,0x78e7930bafd440,-0x450e3835e02d8b0,0x11c955620f136810,-0x2b9e91ee9bf690ec,0x46b9cfb67781adb4,-0x4fa4e290d337ab8c,0x3fa618c48d688dd4,-0x2439848e62f92c6b,0xe81a117e0e8f12d,-0x3f8439157b68637,0xb451ad32c927f1,-0x12f43b131f0b55,0x1011fbd80e8f3,-0x4fb6f0791a1,0x41926ead7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 9 28 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 28 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 19 indices rho q6 m6 6 790272000 11=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 19 indices rho q6 m6 6 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0xea9f7,-0xb4de,0x74e,-0x39,0x1]
def r7 : List ℤ := raw_ints% [-0x1171c4442180,-0x19ac416c7c10,-0x1037e41a797c,-0x5c2782ec318,-0x142e62a4f41,-0x2cccc96f69,-0x3dc64555a,-0x309e6add,-0x10d5cd7]
def m7 : List ℤ := raw_ints% [0x0,-0x531f351808e1ec0,0x2e58fe423aff4f90,-0xb9fafacb6cfb98b0,0x1babdaa26ffb39224,-0x2b6482ed1993ac8bc,0x2f0be10fd79f44884,-0x23ff856b75f6b949c,0x137a803fc7b55ab79,-0x7594e5496b11fd0f,0x1df3282439793fbd,-0x4dd441748ffb0fb,0x74f9f339b38547,-0x55803f30f24d1,0x159d36acf18b,-0xd4c85a49d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 9 30 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 30 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 19 indices rho q7 m7 7 790272000 11=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 19 indices rho q7 m7 7 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x10d5cd7,0xea9f7,-0xb4de,0x74e,-0x39,0x1]
def r8 : List ℤ := raw_ints% [0x1406ffa0a5180,0x1d594c6bc1790,0x127158bc5950c,0x681b4479c0f4,0x169c85004de1,0x31ac4f3469e,0x4394684b99,0x3441e82f0,0x11ab6e0c]
def m8 : List ℤ := raw_ints% [0x0,0x39257480861b5240,-0x1f28b18fc71b86b30,0x79f224a5db90eaf90,-0x11a401eabdb8655f8c,0x1acb55bdfbd370ee14,-0x1c01f623b7b178ec2c,0x148ab534d8972ece34,-0xa9379a1135c31ba53,0x3c2a9dd818a8f5085,-0xe42530b499f87cbf,0x21df5c273bcbe629,-0x2d6112fa9d11e6d,0x1c7c7b4408259b,-0x5d9840078259,0x2b076c745f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 9 32 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 32 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 19 indices rho q8 m8 8 790272000 11=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 19 indices rho q8 m8 8 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x11ab6e0c,-0x10d5cd7,0xea9f7,-0xb4de,0x74e,-0x39,0x1]
def r9 : List ℤ := raw_ints% [-0x150521ed497e00,-0x1eb239589e2fc0,-0x1334eb3de743a0,-0x6bd8a80678fb4,-0x17454b8ae0140,-0x32b494b0facb,-0x4446e903f0a,-0x341ac319af,-0x115119204]
def m9 : List ℤ := raw_ints% [0x0,-0x2749c0185c32c88c0,0x14fb2bcc3ffa6c9b10,-0x503679fc99b2e9ab30,0xb4c937b21a18a9f304,-0x10a5bae035cd960ecdc,0x10cc782423d2f9e9764,-0xbd2a024d8ae8feb0bc,0x5cbcbed70d713c5e71,-0x1f14fb69e65e5e1bd7,0x6d9a95f9c60e83995,-0xeda64a65d3a83b63,0x11b0814d8c37a54f,-0x98092ae1b53209,0x1947a82f27773,-0x8ad7d27f75]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 9 34 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 34 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 19 indices rho q9 m9 9 790272000 11=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 19 indices rho q9 m9 9 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x115119204,0x11ab6e0c,-0x10d5cd7,0xea9f7,-0xb4de,0x74e,-0x39,0x1]
def r10 : List ℤ := raw_ints% [0x1499ac3663f2a00,0x1dff03cf8abd7c0,0x12b3cb477fff950,0x688f7657e148a0,0x16713a9d531908,0x3094fdbf819a4,0x40e3a5e82c6d,0x3104672c80e,0x10148fd54d]
def m10 : List ℤ := raw_ints% [0x0,0x1b02b410bf62e9e040,-0xe262d304c6adaaa9b0,0x34ebdd49d3b48337b10,-0x7451a1e4ba95df3092c,0xa6789bcd98245f81b74,-0xa25ff26ff2ff181c7cc,0x6dc5f555b6f23d52b94,-0x334767aba469b9400fb,0x1033f928ba430a12d1d,-0x3519a5d3ce2b0e2f07,0x68eacaa7ef59522a1,-0x6ec65aba2d7090c5,0x32bf19d7e8c2503,-0x6d05d4cf8ed51,0x1bee00e91a7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 9 36 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 36 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 19 indices rho q10 m10 10 790272000 11=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 19 indices rho q10 m10 10 790272000 11 7
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_10
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<11) : intPolyRF (mz e)=rfPoly (C (790272000:ℚ))*rfX^11*(1-rfX)^7*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V3C12
