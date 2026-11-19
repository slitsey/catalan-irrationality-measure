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
namespace CatalanCore.Li2.NVMod.FamilySource.U2C11
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,2,11,size⟩
def bases : List ℕ := [1,2]
def indices : List ℕ := [3,4,5,6,7,8,9,10,11]
def num : List ℤ := raw_ints% [0x0,0x4,0xc,0xd,0x6,0x1]
def den : List ℤ := raw_ints% [0x1308a80,0x1cedd70,0x130d844,0x725b10,0x1af6af,0x42639,0x6ace,0x6c6,0x3f,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0xa,-0xaf,0x62,-0x62,0x48,-0x1ef]
def rhoDenominators : List ℤ := raw_ints% [0xd20,0x23,0x2,0x3,0x10,0x5,0x5,0x7,0xe0]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-3) 0:ℚ)/(rhoDenominators.getD (m-3) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 2
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 3 12
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
  | 7=>li7
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
def r0 : List ℤ := raw_ints% [0x0,0x4,0xc,0xd,0x6,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0xf9125883cc0,0xc119eea916d0,-0x45215f351d240,0xf23b53f3f86f4,-0x243b989ab315e0,0x3e9c96186c6f40,-0x5080990b202f20,0x4e2b8f9917711d,-0x398e59078dcfc8,0x1ff3b4295555ac,-0xd28e4c5b08538,0x3e71cae644012,-0xcabdeff114d8,0x19bacca14fbc,-0x1b5944b05e8,0x98e51cae5,-0x2973900,0xbd7e00,-0x17afc0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 9 17 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 17 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 20 indices rho q0 m0 0 7745455872000 11=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 20 indices rho q0 m0 0 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m1 : List ℤ := raw_ints% [0x0,0xab3c9cda9c40,-0x803a8357abaf0,0x2c4141df7478c0,-0x952a881e16347c,0x1568c89b4764ea0,-0x2365812d0986840,0x2b65291ad1aa160,-0x28043f9657c60df,0x1bd7c9f61415698,-0xe84612744e02e4,0x5924995ba0cd28,-0x18608966316486,0x47e74253bab48,-0x81a7c82e2914,0x759472f0578,-0x1fdad99077]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 9 18 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 18 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 20 indices rho q1 m1 1 7745455872000 11=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 20 indices rho q1 m1 1 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x75b9abd64b6c0,0x5553a7d6698850,-0x1c7291d411d7040,0x5c6bdd166fef954,-0xcc0c70205f722e0,0x1436028cfe94da40,-0x17aaf50579962520,0x14c269b9250eb5f5,-0xdab09a99c387388,0x6b33dee6638bf4c,-0x265c1c2113ebdb8,0x9abca472879202,-0x19e1ce761a5718,0x294fe865a25dc,-0x1fc0f6c75128,0x69d841bf7d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 9 19 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 19 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 20 indices rho q2 m2 2 7745455872000 11=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 20 indices rho q2 m2 2 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x50efa62353da40,-0x38e4a7d9bebdb70,0x125c0a609ad532c0,-0x399a6c0c18762e9c,0x7a7f5812029905a0,-0xba6affe363dd3940,0xd0dd6f6352bd9260,-0xae831587ad0af427,0x6cdcca4b59d763d8,-0x3237d95aabc70cc4,0x10c2c840a059a1e8,-0x3e4ffda056eefd6,0x971484c14dd308,-0xd4bac5a4f9a74,0x89a6fde92fb8,-0x15dfc17deff]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 9 20 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 20 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 20 indices rho q3 m3 3 7745455872000 11=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 20 indices rho q3 m3 3 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x1]
def r4 : List ℤ := raw_ints% [-0x1308a80,-0x1cedd70,-0x130d844,-0x725b10,-0x1af6af,-0x42635,-0x6ac2,-0x6b9,-0x39]
def m4 : List ℤ := raw_ints% [0x0,-0x37a4c23849a60c0,0x26022a2fa9006dd0,-0xbe508ee53c04ce40,0x241b98cd082ae38b4,-0x4a17c2c98fea917e0,0x6c750beb6dbab1d40,-0x7471fd5981f9c0020,0x5cced4c5bb3f6ec0d,-0x36ea3bc9953ff6548,0x17db73b82088453ec,-0x76ddc6437aee51f8,0x19714ec5fab4ba72,-0x37ca6a1fe90d458,0x450ba811dcc4fc,-0x255ca46dd91e8,0x48022d9e155]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 9 22 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 22 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 20 indices rho q4 m4 4 7745455872000 11=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 20 indices rho q4 m4 4 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x39,0x1]
def r5 : List ℤ := raw_ints% [0x43ced680,0x65dec370,0x421149b4,0x18456e4c,0x58e91e7,0xd18c02,0x13a1a9,0x11754,0x74e]
def m5 : List ℤ := raw_ints% [0x0,0x26414586b2a22840,-0x1970973efddb0b7f0,0x7bc219f2a0165fcc0,-0x16c22542bfc28267bc,0x2d23abf173e13c1ca0,-0x3fa8be6008c8103240,0x4197a7839e94528b60,-0x31eebb2274862fd52f,0x1c0dcd97a851f9ef18,-0xb7c5ccdf4ce256fa4,0x3566659b9e23368a8,-0xa85a1b7e860ee8a6,0x14d3d83bc4655cc8,-0x16917b5c9bec8d4,0xa25b65c505ff8,-0xec172139947]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 9 24 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 24 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 20 indices rho q5 m5 5 7745455872000 11=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 20 indices rho q5 m5 5 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x74e,-0x39,0x1]
def r6 : List ℤ := raw_ints% [-0x8b093b300,-0xcf146b1a0,-0x84cecfd48,-0x30143e52c,-0xacb08406,-0x18c0a277,-0x23aa0c2,-0x1dd8ab,-0xb4de]
def m6 : List ℤ := raw_ints% [0x0,-0x1a4cdfcc9acf7bac0,0x110ed86232914fe750,-0x50c3c9e2c5d4d0fc40,0xe6b95b56dc73942d14,-0x1bb0ebe91a9877e54e0,0x25aec25a01ecae57840,-0x25507cc9c0940a5b320,0x1b2a25768713b395965,-0xe8164e223da4c4e108,0x59994a293e868e3b8c,-0x184b5a3a260abc1c38,0x4672e6142ae62f762,-0x7d9d3dcd92e1ff98,0x76b40d61401631c,-0x2c15b5b3dfe4a8,0x3032ec3a246d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 9 26 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 26 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 20 indices rho q6 m6 6 7745455872000 11=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 20 indices rho q6 m6 6 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0xb4de,0x74e,-0x39,0x1]
def r7 : List ℤ := raw_ints% [0xd7297a1b00,0x13e54831420,0xca6f24a958,0x487e453a98,0x100b911296,0x241c8b568,0x32b4d42d,0x28e76f2,0xea9f7]
def m7 : List ℤ := raw_ints% [0x0,0x1214d9dcaa6ea50640,-0xb751b03d14a99ef070,0x34e31ec479d68f4f6c0,-0x92eeef6ef6440cd67dc,0x1119b9b258f666959ba0,-0x167cef776b6bd219f340,0x156dfdb057b056349c60,-0xeefac1e2c550d8375f7,0x7963ef46a7cebdf0058,-0x2c35cb352a8d131e384,0xb2f35dd76472429968,-0x1dcd33699c66d302f6,0x2fc1c71dd3bdf5888,-0x2732c65bf51cec34,0xbf5b14bbbb4e38,-0x9ce6f2f4e14f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 9 28 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 28 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 20 indices rho q7 m7 7 7745455872000 11=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 20 indices rho q7 m7 7 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0xea9f7,-0xb4de,0x74e,-0x39,0x1]
def r8 : List ℤ := raw_ints% [-0x1171c4442180,-0x19ac416c7c10,-0x1037e41a797c,-0x5c2782ec318,-0x142e62a4f41,-0x2cccc96f69,-0x3dc64555a,-0x309e6add,-0x10d5cd7]
def m8 : List ℤ := raw_ints% [0x0,-0xc6e55c7b52c11744c0,0x7b5527ad0f779b454d0,-0x22beb6ea0bd42505ba40,0x5e06b1230542fe4eae74,-0xaa0b18dfc596fd7529e0,0xd8678e40eee574fb6b40,-0xc6b5f7686ad63728ce20,0x84beea308fc2109e63fd,-0x403170fee52216933ec8,0x161043ca1ab096ba9e2c,-0x534dd7fb2562837f478,0xcbb9a94065df2844d2,-0x124b0c1020a8c210d8,0xcfd22f26d1f4083c,-0x33d7d18ebb6c168,0x1fd26a88b3ec5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 9 30 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 30 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 20 indices rho q8 m8 8 7745455872000 11=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 20 indices rho q8 m8 8 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x10d5cd7,0xea9f7,-0xb4de,0x74e,-0x39,0x1]
def r9 : List ℤ := raw_ints% [0x1406ffa0a5180,0x1d594c6bc1790,0x127158bc5950c,0x681b4479c0f4,0x169c85004de1,0x31ac4f3469e,0x4394684b99,0x3441e82f0,0x11ab6e0c]
def m9 : List ℤ := raw_ints% [0x0,0x88bdaf94c8e4bfff440,-0x531aaa58e56c197fa4f0,0x16e5a4730b70fc0bf20c0,-0x3c72b853537aa945676fc,0x6a532c30aa7aaafa1e2a0,-0x83219ce2401eb9d14bc40,0x742b98c01abed9d7e6560,-0x4a75a8f1c0668bacaf87f,0x224dfd4e932b674a82798,-0xb2164d2716dc9331a064,0x272f6434cc6b1baea428,-0x57d65f713dcc87492c6,0x70d831c50c130d9648,-0x45099152afb651c94,0xe05b94a96b0aa78,-0x66f5f37334917]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 9 32 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 32 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 20 indices rho q9 m9 9 7745455872000 11=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 20 indices rho q9 m9 9 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x11ab6e0c,-0x10d5cd7,0xea9f7,-0xb4de,0x74e,-0x39,0x1]
def r10 : List ℤ := raw_ints% [-0x150521ed497e00,-0x1eb239589e2fc0,-0x1334eb3de743a0,-0x6bd8a80678fb4,-0x17454b8ae0140,-0x32b494b0facb,-0x4446e903f0a,-0x341ac319af,-0x115119204]
def m10 : List ℤ := raw_ints% [0x0,-0x5e0268b64a1d43ff7ec0,0x3814688850787cbfc1650,-0xf2239c41695cd3c078840,0x2708614999817cf693d4d4,-0x42defb9e7066d8a25516e0,0x5007d23318b6427e7e3640,-0x447c6f8c24b3b65d8e5120,0x2a28a378820cd67f1801d5,-0x12847073c0b65721338e88,0x5ac3d82e6deacfbbc63cc,-0x129cda8f3ce6e6e8e2ab8,0x262fb1fcb66192317ec2,-0x2bbfb3d5ca880807818,0x16f934811a96f7bc5c,-0x3c924a001ed0d828,0x14c3a0c9f1b65d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 9 34 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 34 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 20 indices rho q10 m10 10 7745455872000 11=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 20 indices rho q10 m10 10 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x115119204,0x11ab6e0c,-0x10d5cd7,0xea9f7,-0xb4de,0x74e,-0x39,0x1]
def r11 : List ℤ := raw_ints% [0x1499ac3663f2a00,0x1dff03cf8abd7c0,0x12b3cb477fff950,0x688f7657e148a0,0x16713a9d531908,0x3094fdbf819a4,0x40e3a5e82c6d,0x3104672c80e,0x10148fd54d]
def m11 : List ℤ := raw_ints% [0x0,0x40a1a7fd52f41ebfa7240,-0x25e55400b709b0c6d4f570,0xa07cdb31d97d0e15ccfac0,-0x194f636a2d659dd189c9d1c,0x2a4aa8d410213c6a57d31a0,-0x312deaddb233f0de97d4d40,0x28b33b366e97487fdeba660,-0x1815e89db8f2b3d319aeec7,0xa178e8e229ca442001b4d8,-0x2eb64fcf3e31382cae9e44,0x8ebff3e4576d68cb138e8,-0x10b9d5892f87dd5414c16,0x110a756cc8878e0b8608,-0x7a72448ab9c9aab1f4,0x1052218b7f3fc04b8,-0x42d4b00dc6529f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 9 36 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 36 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 20 indices rho q11 m11 11 7745455872000 11=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 20 indices rho q11 m11 11 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x10148fd54d,-0x115119204,0x11ab6e0c,-0x10d5cd7,0xea9f7,-0xb4de,0x74e,-0x39,0x1]
def r12 : List ℤ := raw_ints% [-0x13211ded1c562880,-0x1bc96998b4c7a0b0,-0x1146102f24f1c8b4,-0x603a3a8ee19ba80,-0x14905e5973b8503,-0x2c47a6a590d31d,-0x3ac243e176c52,-0x2c07a0569b21,-0xe4c8f2b5e5]
def m12 : List ℤ := raw_ints% [0x0,-0x2c6f237e2907d523c2e8c0,0x19a439565da8f26a9268bd0,-0x6aa69571f7f9fdcd459e640,0x107a312fd738539e8a10f834,-0x1ae38cf79780cf1b1cd65be0,0x1e6b87bba8e7f7711da41940,-0x185fd8e52bfe94cc2b53fc20,0xde1258fc4673e76312c78ed,-0x58d10bf031ea222dd10c048,0x1843797896f3e0d8e17346c,-0x4502a7e364f669ebc6cef8,0x7602bc2d9b33137822132,-0x6a9e3cc5d2322eca0558,0x28cf4cac4da687f477c,-0x463856f6f007758e8,0xd6974601e36135]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 9 38 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 38 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 20 indices rho q12 m12 12 7745455872000 11=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 20 indices rho q12 m12 12 7745455872000 11 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_12
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<13) : intPolyRF (mz e)=rfPoly (C (7745455872000:ℚ))*rfX^11*(1-rfX)^8*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U2C11
