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
namespace CatalanCore.Li2.NVMod.FamilySource.V3C13
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,3,13,size⟩
def bases : List ℕ := [0,1,2]
def indices : List ℕ := [3,4,5,6,7,8,9,10,11,12]
def num : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def den : List ℤ := raw_ints% [0xe467e00,0x16e2ebc0,0x101900a0,0x68d1d04,0x1b5eb44,0x4cc15b,0x927e1,0xbc16,0x9ba,0x4b,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x5,-0xa,0xf5,-0xc4,0x126,-0x168,0x1545,-0x25d]
def rhoDenominators : List ℤ := raw_ints% [0x2760,0x46,0xe,0x3,0x10,0x5,0x5,0x7,0xe0,0x7e]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-3) 0:ℚ)/(rhoDenominators.getD (m-3) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 3
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 3 13
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤12))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤12 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1]
def omegaDens3 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9]
def omega3 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums3 omegaDens3
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_3 : padCoefficients 13 omega3=padCoefficients 13 (omegaCoefficients 12 3) := by decide +kernel
theorem omega_spec_3 : coefficientsPoly omega3=omegaNumerator 12 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_3
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
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
  | 3=>omega3
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
  change m∈Finset.Ico 3 13 at hb
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x47900ba400,0x394e5952540,-0x1542c9972270,0x4d820c44c880,-0xc1e6800c9b5c,0x1603e984113a0,-0x1df762e4ff1c0,0x1f13de3200c50,-0x18b799a5fb377,0xf0bce451a698,-0x6efc929a7904,0x25f524882fc8,-0x94cadf334f6,0x18a5f998dc8,-0x27f1bbe234,0x206bd1ba8,-0x7c2f64f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 10 19 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 19 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 21 indices rho q0 m0 0 64012032000 12=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 21 indices rho q0 m0 0 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x35ac08bb000,-0x299079c2d0c0,0xee2cc0ec66d0,-0x344773cbfd740,0x7db36a99936f4,-0xdae33d1298fe0,0x11cb5301d33ac0,-0x1191ebca277f60,0xd3f16ba96e37d,-0x79a56363279c8,0x3486ad195e32c,-0x10ae41d4bc0f8,0x3c0508ef9852,-0x8fa76a8a1d8,0xcd04df25bc,-0x8c4a3c8a8,0x19be4f45]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 10 20 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 20 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 21 indices rho q1 m1 1 64012032000 12=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 21 indices rho q1 m1 1 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x2841068c4000,0x1e3348f998c40,-0xa75925deffaf0,0x23729ad656b4c0,-0x520dfc3c615c7c,0x892f219f5a7ca0,-0xaac539aa0324c0,0xa0c41a1ffcb260,-0x730959440e4f7f,0x3e511e4bb83798,-0x193810c79a4764,0x7702a7ae99e28,-0x188dbda6aae46,0x34fb53b05c48,-0x425c2decf14,0x2609354778,-0x54fc1917]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 10 21 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 21 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 21 indices rho q2 m2 2 64012032000 12=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 21 indices rho q2 m2 2 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x1e30c4e930000,-0x15fb3a1e57f6c0,0x75fcf4c0ef8850,-0x182875ede5ae040,0x35ec8c826dfc154,-0x56b0a88be09cce0,0x676d708d57885c0,-0x5cf4bcee4b70f20,0x3f338ff85fc0855,-0x2057b5a00419e88,0xc461a2863deecc,-0x35cbf8fefb22b8,0xa2cf393b31642,-0x13c23eaab5a18,0x15a3f97fdbdc,-0xa533466a28,0x1175a7fdd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 10 22 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 22 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 21 indices rho q3 m3 3 64012032000 12=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 21 indices rho q3 m3 3 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x1]
def r4 : List ℤ := raw_ints% [-0xe467e00,-0x16e2ebc0,-0x101900a0,-0x68d1d04,-0x1b5eb44,-0x4cc15b,-0x927dd,-0xbc0a,-0x9ad,-0x45]
def m4 : List ℤ := raw_ints% [0x0,-0x16a493aee40000,0x1006b1eaebada40,-0x5377156cc79db70,0x108bb23dc06452c0,-0x23ab1e2b34d8b69c,0x37385c30a2a6fba0,-0x3f3aab2b23cd0dc0,0x3651bc98134b7c60,-0x232102172479b8c7,0x10fed795f39260d8,-0x60cfacbc36d8144,0x18a135288f88ce8,-0x4447324769e596,0x771198fe96808,-0x719b43d44874,0x2cda84d42b8,-0x392aa359f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 10 24 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 24 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 21 indices rho q4 m4 4 64012032000 12=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 21 indices rho q4 m4 4 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x45,0x1]
def r5 : List ℤ := raw_ints% [0x3d8fff600,0x61ce30cc0,0x43fda3f60,0x1b3efd174,0x6f7b4c50,0x12fa3243,0x22afe4a,0x298a11,0x1e318,0xa8a]
def m5 : List ℤ := raw_ints% [0x0,0x10fb6ec32b00000,-0xbb415ca0d6e60c0,0x3b3c24cbe6646dd0,-0xb62efc7d0075ae40,0x17bdf06091fb100b4,-0x23723f54f2123b1e0,0x27010f66b28c8f0c0,-0x2010eb212e6500620,0x13be7a46fb8d4006d,-0x90978c0606bef848,0x304ed2e3ff3b236c,-0xb693ffc9eac86f8,0x1cf27958aa202b2,-0x2d3c99ebdcff58,0x257504170c2fc,-0xc2be7170ee8,0xba8070bb5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 10 26 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 26 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 21 indices rho q5 m5 5 64012032000 12=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 21 indices rho q5 m5 5 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0xa8a,-0x45,0x1]
def r6 : List ℤ := raw_ints% [-0x9672ebec00,-0xed5a889f80,-0xa38a9d8980,-0x40cb598cc8,-0x105351a934,-0x2b9727cbe,-0x4d841707,-0x5934192,-0x3cf833,-0x13356]
def m6 : List ℤ := raw_ints% [0x0,-0xcbc931260400000,0x88f6b9551c922840,-0x2a2bac78e61b8b7f0,0x7df5404a57e77dcc0,-0xfe64f8fa4c99f6fbc,0x16ec4eb7a11c6bd2a0,-0x184530cb2bbd6d9ec0,0x131d8cce13616e8560,-0xb374d3bc75d4867cf,0x4dc13921d7e22ac18,-0x1862167a2c0c47c24,0x5588b332194133a8,-0xc65135475b0b266,0x115140f4644f1c8,-0xc6581d3c3d6d4,0x34c9a0d142f8,-0x25e6d73de7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 10 28 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 28 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 21 indices rho q6 m6 6 64012032000 12=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 21 indices rho q6 m6 6 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x13356,0xa8a,-0x45,0x1]
def r7 : List ℤ := raw_ints% [0x112354c85400,0x1ae35e068680,0x1266099d7640,0x739e29601d8,0x1ccf0e60810,0x4bd2576c5e,0x84473bbd8,0x94497a5d,0x61a10ea,0x1d11ff]
def m7 : List ℤ := raw_ints% [0x0,0x98d6e4dc83000000,-0x6454f6a76a437bac0,0x1e1ce81895231fe750,-0x5779a4372a6993dc40,0xab5dda8b3355517514,-0xeee5b9b6522c020ee0,0xf3aa531d7e3c7e33c0,-0xb80be022e4fe7c1920,0x66fdde061a5078efc5,-0x2a43b3efc66f14b408,0xc70ff82161ec10b0c,-0x287cd2d8f5ca85138,0x55afc97765d023a2,-0x6ac4efb489f0a98,0x41d37cd5ff491c,-0xe4997319c1a8,0x7adcc698cd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 10 30 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 30 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 21 indices rho q7 m7 7 64012032000 12=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 21 indices rho q7 m7 7 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1d11ff,-0x13356,0xa8a,-0x45,0x1]
def r8 : List ℤ := raw_ints% [-0x19efd2c958200,-0x2882d3da84040,-0x1b913660bb8e0,-0xac0c2553b4bc,-0x2a808cf2dae4,-0x6ea5bb49c95,-0xbe56ea3dc1,-0xd17431412,-0x86778fe9,-0x26a34cb]
def m8 : List ℤ := raw_ints% [0x0,-0x72a12ba5624000000,0x499aeb00c605a50640,-0x1590beab73f4dbef070,0x3d03120c8aacc8ad6c0,-0x74177d255b39c64efdc,0x9cb01dae531acadf1a0,-0x9a222eb3165c405f7c0,0x6fc24cad283267c3660,-0x3bb0cab96538e85f697,0x1735c296e2f4e2c1d58,-0x669dedd95860fe4804,0x1359abe3e40f9fa468,-0x25537d0456b0d80b6,0x295fc4923ddcad88,-0x15e39dbd3745a34,0x3dc3de2339138,-0x18d230613ef]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 10 32 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 32 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 21 indices rho q8 m8 8 64012032000 12=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 21 indices rho q8 m8 8 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x26a34cb,0x1d11ff,-0x13356,0xa8a,-0x45,0x1]
def r9 : List ℤ := raw_ints% [0x22791dcf7dea00,0x35a5882ebe6f40,0x2457801c8bbea0,0xe18ee8167194c,0x375781bdfaa30,0x8eda0cdef445,0xf31ccd1b6d6,0x107dcfb5fb1,0xa65c26a6c,0x2ea5e790]
def m9 : List ℤ := raw_ints% [0x0,0x55f8e0bc09b0000000,-0x3612e2a2c9dd51744c0,0xf7cbc23d26d3af454d0,-0x2abb35acf87a0d829a40,0x4f135f6736bc6f027674,-0x6774db865b9ed958c3e0,0x6242ae03e6f822498ec0,-0x4475374ad87ed0c09420,0x22ec0b395c42acbc5c5d,-0xcdf10b61d1aa6fcf1c8,0x3569fa2b102fcf36dac,-0x954c9e1d2218586978,0x1061362ac25df39512,-0x101be63c5a4999bd8,0x749b6212080163c,-0x10a81cfeb9be68,0x5004af81d25]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 10 34 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 34 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 21 indices rho q9 m9 9 64012032000 12=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 21 indices rho q9 m9 9 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x2ea5e790,-0x26a34cb,0x1d11ff,-0x13356,0xa8a,-0x45,0x1]
def r10 : List ℤ := raw_ints% [-0x299eafcd958e000,-0x409223445a0f200,-0x2b9474196024ac0,-0x10d429753972fa0,-0x41b324770b98f4,-0xa87044b6d3600,-0x11c3f5d48814b,-0x13140b7def8a,-0xbddcb2eeef,-0x344d86cc4]
def m10 : List ℤ := raw_ints% [0x0,-0x407aa88d07440000000,0x27c7449d9c133bfff440,-0xb26e7375c18dc5ffa4f0,0x1e0c1cea718d8c9d300c0,-0x36253919e49f1ca687efc,0x44bff9d9de0cf9ab858a0,-0x3f1ce05e8cde4c299d8c0,0x2a4992c90a7a1ff431f60,-0x149de8393beeb8c24871f,0x73476c9ad01b23faa498,-0x1c0ef97c89c556281ce4,0x489873492e6826fef28,-0x73c4138d5b1194e486,0x64bf8dd28ef432b48,-0x26d9a838acf46a94,0x47baaa3862cd78,-0x10153a0709b7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 10 36 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 36 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 21 indices rho q10 m10 10 64012032000 12=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 21 indices rho q10 m10 10 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x344d86cc4,0x2ea5e790,-0x26a34cb,0x1d11ff,-0x13356,0xa8a,-0x45,0x1]
def r11 : List ℤ := raw_ints% [0x2eaa4502fb207800,0x4836781251d89f00,0x30961fc5a0c70880,0x12b1155881a59c50,0x48a43eb4c51a070,0xb9352c7612d4b8,0x1366f402403e44,0x14a977d30c78d,0xcb79593fade,0x374eb4ee7d]
def m11 : List ℤ := raw_ints% [0x0,0x305bfe69c57300000000,-0x1d4cb5c6a045883ff7ec0,0x80d0049c7433a08fc1650,-0x15358a5acae78aaa9a6840,0x2543237f8fc6fceab61cd4,-0x2df85b8b0fc6ec633d90e0,0x28d4dff6d2165591a541c0,-0x1a556e316f2f4236a27720,0xc471a84161489016f3c35,-0x411b87d0ea1fb12ec2188,0xeddf770042110765334c,-0x2392145cec66c9925fb8,0x336ff85f930be2cf302,-0x278200362dcc308318,0xcf24824db65a325c,-0x134451065427528,0x3399d3b85ebd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 10 38 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 38 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 21 indices rho q11 m11 11 64012032000 12=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 21 indices rho q11 m11 11 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x374eb4ee7d,-0x344d86cc4,0x2ea5e790,-0x26a34cb,0x1d11ff,-0x13356,0xa8a,-0x45,0x1]
def r12 : List ℤ := raw_ints% [-0x31588a341198f8600,-0x4c31fb1f16bd924c0,-0x3321ba911f9716f20,-0x139bebc4061e9da74,-0x4beb197398b77be4,-0xc0adfcae2e762ff,-0x1412cc9a9acd225,-0x153b99a0700c7a,-0xcf5c0ea6e445,-0x37c796de3c1]
def m12 : List ℤ := raw_ints% [0x0,-0x2444fecf5416400000000,0x159b85ec41ea08ebfa7240,-0x5d380456e0fb3928d4f570,0xf06839f2f8473201b6dac0,-0x19c493973abefb9f4d1251c,0x1eec0bef39ea3e1a6a5c7a0,-0x1a99e66beff5404020c01c0,0x1086f814862a81f38838060,-0x75f7d7731d442fd9ccab67,0x251618a5a6e07a8c9d11d8,-0x7f11f775f44b713ddf2c4,0x118d791277855dcd043e8,-0x16f92b724fb68635d1d6,0xf8858631aa7226db08,-0x45040118d95f15ff4,0x52a336281c187b8,-0xa5333ae8613f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 10 40 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 40 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 21 indices rho q12 m12 12 64012032000 12=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 21 indices rho q12 m12 12 64012032000 12 8
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_12
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<13) : intPolyRF (mz e)=rfPoly (C (64012032000:ℚ))*rfX^12*(1-rfX)^8*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V3C13
