module
public import CatalanCore.Li2.NVMod.EndpointSeries
public import CatalanCore.Li2.NVMod.AtInfinity
public import CatalanCore.Li2.NVMod.EndpointLists
public import CatalanCore.Li2.NVMod.EndpointOne
public import CatalanCore.Li2.NVMod.EndpointUnits
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section
structure EndpointInput where
  key : TypeKey
  p : ℕ
  D : ℕ
  clearZ : ℕ
  clearOne : ℕ
  v0 : ℕ
  v1 : ℕ
  D_pos : 0<D
  mz : ℕ→ℤ[X]
  moment_clear : ∀ i j : Fin key.size,
    intPolyRF (mz (i.val+j.val))=rfPoly (C (D:ℚ))*
      rfX^clearZ*(1-rfX)^clearOne*momentRF key (X^(i.val+j.val))
  order_zero : (v0:ℤ)=(clearZ:ℤ)*key.size+zeroOrder key
  order_one : (v1:ℤ)=(clearOne:ℤ)*key.size+oneOrder key
  factorials : FactorialDetChecked key

def EndpointInput.F (I : EndpointInput) : ℤ[X] :=
  (Matrix.of fun i j : Fin I.key.size=>I.mz (i.val+j.val)).det
def chk0 (I : EndpointInput) : Bool :=
  (topPoles I.key).length == I.key.size &&
    ratUnitCheck I.p ((I.D:ℚ)^I.key.size*zeroLead I.key)
def chk1 (I : EndpointInput) : Bool :=
  match oneLead I.key with
  | none=>false
  | some q=>ratUnitCheck I.p ((I.D:ℚ)^I.key.size*q)
def chkInf (I : EndpointInput) : Bool :=
  decide (I.key.size≤(slots I.key).length) &&
    ratUnitCheck I.p ((I.D:ℚ)^I.key.size*infLead I.key)

def intPolyRFHom : ℤ[X]→+*RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem EndpointInput.rf_det (I : EndpointInput) :
    intPolyRF I.F=(rfPoly (C (I.D:ℚ))*rfX^I.clearZ*(1-rfX)^I.clearOne)^I.key.size*
      constantRF I.key := by
  change intPolyRFHom I.F=_
  rw [EndpointInput.F,RingHom.map_det]
  have hmat : intPolyRFHom.mapMatrix (Matrix.of fun i j : Fin I.key.size=>I.mz (i.val+j.val))=
      (rfPoly (C (I.D:ℚ))*rfX^I.clearZ*(1-rfX)^I.clearOne) •
        (Matrix.of fun i j : Fin I.key.size=>momentRF I.key (X^(i.val+j.val))) := by
    apply Matrix.ext
    intro i j
    exact I.moment_clear i j
  rw [hmat,Matrix.det_smul,Fintype.card_fin]
  rfl

theorem chk0_sound (I : EndpointInput) [Fact I.p.Prime] (h : chk0 I=true) :
    Oge (atZero (constantRF I.key)) (zeroOrder I.key) ∧
      ‖((((I.D:ℚ)^I.key.size)*(atZero (constantRF I.key)).coeff (zeroOrder I.key):ℚ):Padic I.p)‖=1 := by
  have hh : (topPoles I.key).length=I.key.size ∧
      ratUnitCheck I.p ((I.D:ℚ)^I.key.size*zeroLead I.key)=true := by simpa [chk0] using h
  have hz := hankel_zero_lead I.key hh.1
  refine ⟨hz.1,?_⟩
  rw [hz.2]
  exact ratUnitCheck_sound I.p _ hh.2

theorem chk1_sound (I : EndpointInput) [Fact I.p.Prime] (h : chk1 I=true) :
    Oge (atOne (constantRF I.key)) (oneOrder I.key) ∧
      ‖((((I.D:ℚ)^I.key.size)*(atOne (constantRF I.key)).coeff (oneOrder I.key):ℚ):Padic I.p)‖=1 := by
  unfold chk1 at h
  cases hl : oneLead I.key with
  | none => simp [hl] at h
  | some q =>
    simp only [hl] at h
    have ho := hankel_one_lead I.key I.factorials q hl
    refine ⟨ho.1,?_⟩
    rw [ho.2]
    exact ratUnitCheck_sound I.p _ h

theorem chkInf_sound (I : EndpointInput) [Fact I.p.Prime] (h : chkInf I=true) :
    Oge (atInf (constantRF I.key)) (infOrder I.key) ∧
      ‖((((I.D:ℚ)^I.key.size)*(atInf (constantRF I.key)).coeff (infOrder I.key):ℚ):Padic I.p)‖=1 := by
  have hh : I.key.size≤(slots I.key).length ∧
      ratUnitCheck I.p ((I.D:ℚ)^I.key.size*infLead I.key)=true := by simpa [chkInf] using h
  have hi := hankel_at_infinity I.key hh.1
  refine ⟨hi.1,?_⟩
  rw [hi.2]
  exact ratUnitCheck_sound I.p _ hh.2

theorem padic_int_not_dvd_of_unit (p : ℕ) [Fact p.Prime] (z : ℤ) (h : ‖(z:Padic p)‖=1) :
    ¬(p:ℤ)∣z := by
  intro hd
  have hh := Padic.norm_intCast_lt_one_iff.mpr hd
  rw [h] at hh
  exact (lt_irrefl (1:ℝ)) hh

theorem extract_zero_endpoint (P : ℤ[X]) (p n : ℕ) [Fact p.Prime]
    (ho : Oge (atZero (intPolyRF P)) (n:ℤ))
    (hu : ‖((atZero (intPolyRF P)).coeff (n:ℤ):Padic p)‖=1) :
    X^n∣P ∧ ¬(p:ℤ)∣P.coeff n := by
  constructor
  · apply Polynomial.X_pow_dvd_iff.mpr
    intro k hk
    have hh := ho (k:ℤ) (by exact_mod_cast hk)
    rw [intPolyRF_atZero_coeff] at hh
    exact_mod_cast hh
  · rw [intPolyRF_atZero_coeff,Rat.cast_intCast] at hu
    exact padic_int_not_dvd_of_unit p _ hu

theorem extract_one_endpoint (P : ℤ[X]) (p n : ℕ) [Fact p.Prime]
    (ho : Oge (atOne (intPolyRF P)) (n:ℤ))
    (hu : ‖((atOne (intPolyRF P)).coeff (n:ℤ):Padic p)‖=1) :
    (X-1)^n∣P ∧ ¬(p:ℤ)∣(P.comp (X+1)).coeff n := by
  have hd : X^n∣P.comp (X+1) := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro k hk
    have hh := ho (k:ℤ) (by exact_mod_cast hk)
    rw [intPolyRF_atOne_coeff] at hh
    have hc : ((P.comp (X+1)).coeff k:ℚ)=0 :=
      (mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ (by norm_num))
    exact_mod_cast hc
  constructor
  · obtain ⟨R,hR⟩ := hd
    refine ⟨R.comp (X-1),?_⟩
    have he := congrArg (fun Q : ℤ[X]=>Q.comp (X-1)) hR
    have hx : (X+1:ℤ[X]).comp (X-1)=X := by simp
    simpa only [Polynomial.comp_assoc,hx,Polynomial.comp_X,Polynomial.mul_comp,
      Polynomial.pow_comp,Polynomial.X_comp] using he
  · rw [intPolyRF_atOne_coeff,Rat.cast_mul,Rat.cast_intCast,Rat.cast_pow,
      Rat.cast_neg,Rat.cast_one,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one] at hu
    exact padic_int_not_dvd_of_unit p _ hu

theorem intPolyRF_atInf_order (P : ℤ[X]) : Oge (atInf (intPolyRF P)) (-(P.natDegree:ℤ)) := by
  intro e he
  have hen : (((-e).toNat:ℕ):ℤ)= -e := Int.toNat_of_nonneg (by omega)
  have heq : e= -(((-e).toNat:ℕ):ℤ) := by omega
  rw [heq,intPolyRF_atInf_coeff,Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),Int.cast_zero]

theorem extract_inf_endpoint (P : ℤ[X]) (p : ℕ) [Fact p.Prime] (e : ℤ)
    (ho : Oge (atInf (intPolyRF P)) e)
    (hu : ‖((atInf (intPolyRF P)).coeff e:Padic p)‖=1) : ¬(p:ℤ)∣P.leadingCoeff := by
  have hc : (atInf (intPolyRF P)).coeff e≠0 := by
    intro hz
    rw [hz,Rat.cast_zero,norm_zero] at hu
    norm_num at hu
  have hp : P≠0 := by
    intro hz
    apply hc
    simp only [hz,intPolyRF,Polynomial.map_zero,atInf_rfPoly,map_zero,HahnSeries.coeff_zero]
  have hlead : (atInf (intPolyRF P)).coeff (-(P.natDegree:ℤ))≠0 := by
    rw [intPolyRF_atInf_coeff,Polynomial.coeff_natDegree]
    exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hp
  have hle : e≤ -(P.natDegree:ℤ) := le_of_not_gt (fun h=>hlead (ho _ h))
  have hge : -(P.natDegree:ℤ)≤e := le_of_not_gt (fun h=>hc (intPolyRF_atInf_order P _ h))
  have he : e= -(P.natDegree:ℤ) := le_antisymm hle hge
  rw [he,intPolyRF_atInf_coeff,Polynomial.coeff_natDegree,Rat.cast_intCast] at hu
  exact padic_int_not_dvd_of_unit p _ hu

theorem map_rfPoly_C (φ : RatFunc ℚ→+*HahnSeries ℤ ℚ) (q : ℚ) :
    φ (rfPoly (C q))=HahnSeries.C q := by
  have he : rfPoly (C q)=algebraMap ℚ (RatFunc ℚ) q := by
    simpa [rfPoly] using (RatFunc.algebraMap_apply (K:=ℚ) q).symm
  rw [he]
  simp only [eq_ratCast,map_ratCast]

theorem EndpointInput.map_F (I : EndpointInput) (φ : RatFunc ℚ→+*HahnSeries ℤ ℚ) (x : HahnSeries ℤ ℚ)
    (hX : φ rfX=x) :
    φ (intPolyRF I.F)=(HahnSeries.C (I.D:ℚ)*x^I.clearZ*(1-x)^I.clearOne)^I.key.size*
      φ (constantRF I.key) := by
  rw [I.rf_det]
  simp only [map_mul,map_pow,map_sub,map_one,map_rfPoly_C,hX]

theorem EndpointInput.atZero_F (I : EndpointInput) :
    atZero (intPolyRF I.F)=
      (HahnSeries.C (I.D:ℚ)*hX^I.clearZ*(1-hX)^I.clearOne)^I.key.size*atZero (constantRF I.key) := by
  simp only [atZero_eq_hom]
  apply I.map_F
  rw [←atZero_eq_hom]
  exact (atZero_rfPoly X).trans polyHahnQ_X

theorem EndpointInput.atOne_F (I : EndpointInput) :
    atOne (intPolyRF I.F)=
      (HahnSeries.C (I.D:ℚ)*(1-hX)^I.clearZ*hX^I.clearOne)^I.key.size*atOne (constantRF I.key) := by
  have hx : affineRFHahnQ 1 (-1) (by norm_num) rfX=(1-hX : HahnSeries ℤ ℚ) := by
    rw [←atOne_eq_hom]
    simp only [rfX,atOne_rfPoly,Polynomial.X_comp,map_sub,map_one,polyHahnQ_X]
  have hh := I.map_F (affineRFHahnQ 1 (-1) (by norm_num)) (1-hX) hx
  simpa only [←atOne_eq_hom,sub_sub_cancel] using hh

theorem EndpointInput.atInf_F (I : EndpointInput) :
    atInf (intPolyRF I.F)=
      (HahnSeries.C (I.D:ℚ)*hX⁻¹^I.clearZ*(1-hX⁻¹)^I.clearOne)^I.key.size*atInf (constantRF I.key) := by
  simp only [atInf_eq_hom]
  apply I.map_F
  rw [←atInf_eq_hom,rfX,atInf_rfPoly]
  simp [infPolyHahnQ]

theorem checked_zero_initial (I : EndpointInput) [Fact I.p.Prime] (h : chk0 I=true) :
    Oge (atZero (intPolyRF I.F)) (I.v0:ℤ) ∧
      ‖((atZero (intPolyRF I.F)).coeff (I.v0:ℤ):Padic I.p)‖=1 := by
  have hc := chk0_sound I h
  have hs := clearing_initial hX (1-hX) (atZero (constantRF I.key)) (I.D:ℚ)
    I.clearZ I.clearOne I.key.size 1 0 (zeroOrder I.key)
    hX_initial.1 one_sub_hX_initial.1 hc.1
  dsimp only at hs
  have he : (I.key.size:ℤ)*((I.clearZ:ℤ)*1+(I.clearOne:ℤ)*0)+zeroOrder I.key=(I.v0:ℤ) := by
    rw [I.order_zero]
    ring
  rw [he,←I.atZero_F] at hs
  refine ⟨hs.1,?_⟩
  rw [hs.2,hX_initial.2,one_sub_hX_initial.2]
  simpa only [one_pow,mul_one] using hc.2

theorem checked_one_initial (I : EndpointInput) [Fact I.p.Prime] (h : chk1 I=true) :
    Oge (atOne (intPolyRF I.F)) (I.v1:ℤ) ∧
      ‖((atOne (intPolyRF I.F)).coeff (I.v1:ℤ):Padic I.p)‖=1 := by
  have hc := chk1_sound I h
  have hs := clearing_initial (1-hX) hX (atOne (constantRF I.key)) (I.D:ℚ)
    I.clearZ I.clearOne I.key.size 0 1 (oneOrder I.key)
    one_sub_hX_initial.1 hX_initial.1 hc.1
  dsimp only at hs
  have he : (I.key.size:ℤ)*((I.clearZ:ℤ)*0+(I.clearOne:ℤ)*1)+oneOrder I.key=(I.v1:ℤ) := by
    rw [I.order_one]
    ring
  rw [he,←I.atOne_F] at hs
  refine ⟨hs.1,?_⟩
  rw [hs.2,one_sub_hX_initial.2,hX_initial.2]
  simpa only [one_pow,mul_one] using hc.2

theorem checked_inf_initial (I : EndpointInput) [Fact I.p.Prime] (h : chkInf I=true) :
    ∃ e : ℤ, Oge (atInf (intPolyRF I.F)) e ∧
      ‖((atInf (intPolyRF I.F)).coeff e:Padic I.p)‖=1 := by
  have hc := chkInf_sound I h
  have hs := clearing_initial hX⁻¹ (1-hX⁻¹) (atInf (constantRF I.key)) (I.D:ℚ)
    I.clearZ I.clearOne I.key.size (-1) (-1) (infOrder I.key)
    inv_hX_initial.1 one_sub_inv_hX_initial.1 hc.1
  dsimp only at hs
  rw [←I.atInf_F] at hs
  refine ⟨_,hs.1,?_⟩
  rw [hs.2,inv_hX_initial.2,one_sub_inv_hX_initial.2]
  simpa only [one_pow,mul_one,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_one,
    norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one] using hc.2

theorem endpoint_check_sound (I : EndpointInput) [Fact I.p.Prime]
    (h0 : chk0 I=true) (h1 : chk1 I=true) (hInf : chkInf I=true) :
    X^I.v0∣I.F ∧ (X-1)^I.v1∣I.F ∧
      ¬(I.p:ℤ)∣I.F.coeff I.v0 ∧
      ¬(I.p:ℤ)∣(I.F.comp (X+1)).coeff I.v1 ∧
      ¬(I.p:ℤ)∣I.F.leadingCoeff := by
  have hzero := checked_zero_initial I h0
  have hone := checked_one_initial I h1
  obtain ⟨e,hord,hunit⟩ := checked_inf_initial I hInf
  have hz := extract_zero_endpoint I.F I.p I.v0 hzero.1 hzero.2
  have ho := extract_one_endpoint I.F I.p I.v1 hone.1 hone.2
  exact ⟨hz.1,ho.1,hz.2,ho.2,extract_inf_endpoint I.F I.p e hord hunit⟩


#print axioms EndpointInput.rf_det
#print axioms ratDet_sound
#print axioms ratUnitCheck_sound
#print axioms endpoint_check_sound
end
end CatalanCore.Li2.NVMod
