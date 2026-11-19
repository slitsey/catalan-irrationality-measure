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
namespace CatalanCore.Li2.NVMod.FamilySource.U3C12
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,3,12,size⟩
def bases : List ℕ := [1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12]
def num : List ℤ := raw_ints% [0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x4c22a00,0x60aeb40,0x35a0720,0x111074c,0x36f6a8,0x74391,0xa170,0x8e2,0x48,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x4,-0xf,0x8c,-0x4c9,0x1b90,-0x6e4,0x1ef0,-0x3fcf]
def rhoDenominators : List ℤ := raw_ints% [0x118,0x7,0x1,0x1,0x2,0x5,0x1,0x7,0x38]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 3
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 13
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤12))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤12 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 13 omega4=padCoefficients 13 (omegaCoefficients 12 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 12 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 13 omega5=padCoefficients 13 (omegaCoefficients 12 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 12 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 13 omega6=padCoefficients 13 (omegaCoefficients 12 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 12 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 13 omega7=padCoefficients 13 (omegaCoefficients 12 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 12 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 13 omega8=padCoefficients 13 (omegaCoefficients 12 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 12 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 13 omega9=padCoefficients 13 (omegaCoefficients 12 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 12 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 13 omega10=padCoefficients 13 (omegaCoefficients 12 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 12 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 13 omega11=padCoefficients 13 (omegaCoefficients 12 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 12 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 13 omega12=padCoefficients 13 (omegaCoefficients 12 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 12 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
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
  | 4=>omega4
  | 5=>omega5
  | 6=>omega6
  | 7=>omega7
  | 8=>omega8
  | 9=>omega9
  | 10=>omega10
  | 11=>omega11
  | 12=>omega12
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 12 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 4 13 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_4
  · exact omega_spec_5
  · exact omega_spec_6
  · exact omega_spec_7
  · exact omega_spec_8
  · exact omega_spec_9
  · exact omega_spec_10
  · exact omega_spec_11
  · exact omega_spec_12
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
def r0 : List ℤ := raw_ints% [0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0xe450d1237b00,0xa5f08e4e07940,-0x377d98cabae100,0xb4e0ed80909350,-0x190d064dbd34580,0x27dd12e3376ce80,-0x2ee5d49aef73280,0x295a1859d9dad34,-0x1b647cf389bc120,0xd864001847dcb0,-0x4e1998616e2be0,0x13e6cc34806858,-0x36007666867e0,0x57d9964ce530,-0x4583e7a6d20,0xf4b2ba1b4,0x14b9c80,-0xa5ce40,0x2f5f80,-0x5ebf0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 9 19 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 19 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 21 indices rho q0 m0 0 860606208000 12=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 21 indices rho q0 m0 0 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m1 : List ℤ := raw_ints% [0x0,0xab3c9cda9c400,-0x78fed42a782f00,0x2744a6de32b2c00,-0x7bfacb0c79d97c0,0x1097f04aa3e34a00,-0x1973433ab02e2600,0x1cc4a15553e40e00,-0x184804fe98841570,0xf53983fc5b9f580,-0x72b66966f9d2c40,0x26f0c7c3c463680,-0x93df4c08f70d60,0x17099ede86e880,-0x21b7acc5ae540,0x172ae92efb80,-0x41f29b36f0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 9 20 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 20 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 21 indices rho q1 m1 1 860606208000 12=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 21 indices rho q1 m1 1 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% [0x1]
def r2 : List ℤ := raw_ints% [-0x4c22a00,-0x60aeb40,-0x35a0720,-0x1110728,-0x36f624,-0x742d0,-0xa0e0,-0x8a8,-0x3c]
def m2 : List ℤ := raw_ints% [0x0,-0x806d75a3f53000,0x585e479cd0db400,-0x1be0b683a1b3b000,0x556205e1e703fd00,-0xb0f3e60a8888e000,0x105ef58ada5bbc000,-0x11cd37b4405858800,0xe65c3a74654e4140,-0x8aa9db3b829ab200,0x3d7c87eff76ca300,-0x13a1d6525309ce00,0x456524f6ba4a080,-0x9eab8ffa008e00,0xd0541d4e47700,-0x7bb4d31fca00,0x11b7f6ab340]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 9 22 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 22 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 21 indices rho q2 m2 2 860606208000 12=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 21 indices rho q2 m2 2 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [-0x3c,0x1]
def r3 : List ℤ := raw_ints% [0x11d81d800,0x165ccf900,0xc30ec040,0x3ca3aeb0,0xbd0c838,0x17cdfd8,0x1e9370,0x17418,0x838]
def m3 : List ℤ := raw_ints% [0x0,0x6052183af7e4000,-0x40a4218b8642f000,0x13da5e369f0b5a000,-0x3b126755802e59c00,0x76a53d16d146bb800,-0xa9b81f87fed6d5000,0xb1bdbbc1bd7d9b000,-0x89e1ddc6fee007f00,0x4f353e13b81af0000,-0x214ea73c48eacac00,0xa00a7aa893a04000,-0x20e3a0fa6addae00,0x44de22c40756800,-0x50e0391e4b5c00,0x29504489d9000,-0x4bfae6f6f00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 9 24 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 24 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 21 indices rho q3 m3 3 860606208000 12=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 21 indices rho q3 m3 3 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x838,-0x3c,0x1]
def r4 : List ℤ := raw_ints% [-0x271bc93000,-0x308c3b9e00,-0x1a261d9600,-0x800e53860,-0x187178610,-0x2fe28780,-0x3b1f0a8,-0x2a6e00,-0xdba8]
def m4 : List ℤ := raw_ints% [0x0,-0x483d922c39eb0000,0x2f5b534bb54f2c000,-0xe2e400120b5eda000,0x290cc23fa64566d000,-0x5002e46f05332bc800,0x6ebe4626208d568000,-0x6fd28eaa2e684f8000,0x5348137877321c9400,-0x2db07dc84429b60000,0x1239df4698e4d97000,-0x525c5f1095b99b000,0xfbb6e4f853a82800,-0x1e1dbdff2696f800,0x1f89db384447000,-0xdccc1cf5d7000,0x1450f0055400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 9 26 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 26 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 21 indices rho q4 m4 4 860606208000 12=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 21 indices rho q4 m4 4 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0xdba8,0x838,-0x3c,0x1]
def r5 : List ℤ := raw_ints% [0x41539599000,0x50832a0f200,0x2afaaf16f00,0xd01e4d37e0,0x27282e5de0,0x4b479dc18,0x5aa23a00,0x3ed39a8,0x135940]
def m5 : List ℤ := raw_ints% [0x0,0x362e2da12b7040000,-0x22bea670e3674b8000,0xa28859a822d950e000,-0x1ca5de5a5cdb9d5c000,0x36423ce6b2584b8d800,-0x48c0981ad67ad50e000,0x46e7db855110afb9000,-0x32be928115c3244f000,0x1a9a8970b88295d5800,-0xa1212cb7f4a026a000,0x2aca1b0a7ca2844800,-0x7972c5c5b97aae000,0xd42881fd7aa5f000,-0xc585618fc2b8000,0x49bc2a342b2800,-0x56ba6607f000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 9 28 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 28 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 21 indices rho q5 m5 5 860606208000 12=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 21 indices rho q5 m5 5 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x135940,-0xdba8,0x838,-0x3c,0x1]
def r6 : List ℤ := raw_ints% [-0x5c11cf248000,-0x70d58aea8000,-0x3bd177baf600,-0x11f30f7dd000,-0x35759a8da20,-0x6563e2ef60,-0x77f1e6fe8,-0x513c9080,-0x183e058]
def m6 : List ℤ := raw_ints% [0x0,-0x28a2a238e094300000,0x1986f84f3d67a9d8000,-0x74c0c69ae7de9e9a000,0x14133480cf5712630000,-0x24fe318c0d90111d0800,0x301ba0ae9faf05a8e000,-0x2d4d88503815b22c8000,0x1f2e6332b671fbaac000,-0xfa1973c0dab4eb57000,0x59dc36f17db5659c000,-0x166e96e9f3a51dd4000,0x3b11fa214510330000,-0x5dfc2c57bb1444800,0x4d8d9dde3a5de000,-0x189c262ff3fe000,0x1717b633b4000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 9 30 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 30 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 21 indices rho q6 m6 6 860606208000 12=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 21 indices rho q6 m6 6 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x183e058,0x135940,-0xdba8,0x838,-0x3c,0x1]
def r7 : List ℤ := raw_ints% [0x735b1057e7000,0x8cbbb74345e00,0x4a33327a3f300,0x161dbd4660c20,0x4153fb31f9c0,0x7aa28283fb8,0x8f35e68f20,0x5f6505dc8,0x1bda8840]
def m7 : List ℤ := raw_ints% [0x0,0x1e79f9aaa86f2400000,-0x12c7b71fb303c1388000,0x541744dd8d9dec01e000,-0xe1f82ff8f2d24c450000,0x195a1c5daf4aec54b1800,-0x20034fc4f2e98c979a000,0x1d2849843115a52aa9000,-0x13511573a0773b0fd4000,0x943b7e70e767fc9c8800,-0x328fb343b342b24ac000,0xbdc53f2a0dc277e7800,-0x1cf23d336af5b9fc000,0x29dcf54a7e441b0000,-0x1e865363ea0f62000,0x8350e345f067800,-0x62311869f0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 9 32 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 32 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 21 indices rho q7 m7 7 860606208000 12=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 21 indices rho q7 m7 7 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1bda8840,-0x183e058,0x135940,-0xdba8,0x838,-0x3c,0x1]
def r8 : List ℤ := raw_ints% [-0x848a4e1ada8000,-0xa119a25eb66000,-0x548f77a7566a00,-0x1911a363364000,-0x499132f70dde0,-0x88ffb6fdf280,-0x9e677239c48,-0x683547b960,-0x1df25f438]
def m8 : List ℤ := raw_ints% [0x0,-0x16db7b3ffe535b000000,0xdd57f34b5abf22dd8000,-0x3cb85616976ff30e4a000,0x9f932c5a7664cc3c80000,-0x1175f5d21c436a9c63c800,0x156ebe840fa1f6bc746000,-0x12e6246494337a4d7d8000,0xc0fa550aa29b791710000,-0x58988269308e9b3950000,0x1cb137ca7dcc12fea4000,-0x65275c4513e77253b000,0xe4879d3986caaca0000,-0x12bcbdc8760b95df800,0xc098c6ae5bb6ee000,-0x2bbfe8adabf57000,0x1a0c4936540000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 9 34 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 34 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 21 indices rho q8 m8 8 860606208000 12=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 21 indices rho q8 m8 8 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x1df25f438,0x1bda8840,-0x183e058,0x135940,-0xdba8,0x838,-0x3c,0x1]
def r9 : List ℤ := raw_ints% [0x8e801302c813000,0xacac9366001f600,0x5a4d8e81365af00,0x1aa75aa11539ea0,0x4dce070a2fd4c0,0x8ff6cd1811dd8,0xa528c8341e00,0x6b9b7ffbd28,0x1e8d64f660]
def m9 : List ℤ := raw_ints% [0x0,0x11249c6ffebe844000000,-0xa33ec6f6cd93c80c48000,0x2bf36a2e39ced3af72e000,-0x7118cc6e03355cb0410000,0xc1558f06655e9ebf515800,-0xe6ef0dc972398a15fca000,0xc5565cd92518cdaa949000,-0x796910a755665134f84000,0x356194ce77b9b3ad27b800,-0x106a51b169bad997b6c000,0x36550313ed38a5d4ca800,-0x717cc3d45f2fbee3c000,0x86c15205c778b741000,-0x4c0eaa7fb86ccf2000,0xe8f38b566912c800,-0x6e5efe1cf00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 9 36 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 36 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 21 indices rho q9 m9 9 860606208000 12=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 21 indices rho q9 m9 9 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x1e8d64f660,-0x1df25f438,0x1bda8840,-0x183e058,0x135940,-0xdba8,0x838,-0x3c,0x1]
def r10 : List ℤ := raw_ints% [-0x9161bd8ec52bc000,-0xafb5f5f6baa68800,-0x5b9bf4dacd197600,-0x1af0ceb265b01580,-0x4e4cd8db5ee5060,-0x90200b351ad7a0,-0xa44dd899d0c28,-0x6a3b32a062c0,-0x1de0c658dd8]
def m10 : List ℤ := raw_ints% [0x0,-0xcdb7553ff0ee330000000,0x7888e48fecb9e197718000,-0x1fe2e0f4cb39ab7642fa000,0x506f0e4a6eadda396840000,-0x8668527dfd570c54c248800,0x9c65b11f2e455410aea6000,-0x81a21e671e8858440ec8000,0x4cf225c399dc31e6d720000,-0x206a25ff00ac56f526f1000,0x9770a0c806615873b5c000,-0x1d64fd6dab847ab4a3a000,0x38b076847048bfac60000,-0x3ccb78d1c46817c22800,0x1e10adcae18e86e6000,-0x4d6e2b91882e28000,0x1d2ea90d3400000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 9 38 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 38 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 21 indices rho q10 m10 10 860606208000 12=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 21 indices rho q10 m10 10 860606208000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_10
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<11) : intPolyRF (mz e)=rfPoly (C (860606208000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U3C12
