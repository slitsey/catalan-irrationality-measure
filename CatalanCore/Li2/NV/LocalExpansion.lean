module
public import CatalanCore.Li2.NV.Decomposition
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P020
public import CatalanCore.Li2.Port.Unified.Modular.Base.RestrictedPoleMultiplierError
public import CatalanCore.Li2.NV.Classes
public import CatalanCore.Li2.NVMod.Series
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped nonZeroDivisors
open Polynomial Finset Filter
open scoped BigOperators Topology
namespace CatalanCore.Li2.NV
open NVMod
noncomputable section
noncomputable def germSeries (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) : HahnSeries ℤ (Padic ℓ):=
  HahnSeries.ofPowerSeries ℤ (Padic ℓ) (PowerSeries.mk (fun j=>(H j:Padic ℓ)*(ℓ:Padic ℓ)^j))
noncomputable def atZeroPadic (ℓ : ℕ) [Fact ℓ.Prime] (F : RatFunc ℚ) : HahnSeries ℤ (Padic ℓ):=
  expandRF F hX
noncomputable def atLocal (F : RatFunc ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (s : Fin ℓ) : HahnSeries ℤ (Padic ℓ):=
  expandRF F (HahnSeries.single 0 (-(s:Padic ℓ))+HahnSeries.single 0 (ℓ:Padic ℓ)*hX)
noncomputable def kappaQ (n ℓ : ℕ) (s : Fin ℓ) : ℚ:=
  (∏ i∈(Finset.Icc 1 n).filter (fun i=>i%ℓ≠s.val),((i:ℚ)-s)^3)/
    ∏ j∈(Finset.Icc 1 (4*n)).filter (fun j=>j%ℓ≠s.val),((j:ℚ)-s)
noncomputable def kappa (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) : Padic ℓ:=(kappaQ n ℓ s:Padic ℓ)
noncomputable def uQ (z : ℚ) (n ℓ : ℕ) (s : Fin ℓ) : ℚ:=
  (if s.val=0 then 1 else -(s:ℚ)*z^(-(s:ℤ)))*
    kappaQ n ℓ s*(crtPi n ℓ s).eval (-(s:ℚ))^2
def classKey (n ℓ : ℕ) (s : Fin ℓ) : TypeKey:=
  ⟨if s.val=0 then .U else .V,a n ℓ s,c n ℓ s,m n ℓ s⟩
noncomputable def classWeight (n ℓ : ℕ) (s : Fin ℓ) : RatFunc ℚ:=
  if s.val=0 then (rfX:RatFunc ℚ)⁻¹*weight (classKey n ℓ s) else weight (classKey n ℓ s)
def chi (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (Ψ : Germ ℓ) (j : ℕ) : PadicInt ℓ:=
  if s.val=0 then Ψ j else -(s.val:PadicInt ℓ)*Ψ j+if j=0 then 0 else Ψ (j-1)
noncomputable def pairRF (n ℓ : ℕ) (P Q : Ix n ℓ) : RatFunc ℚ:=
  W n*rfPoly (crtE n ℓ P*crtE n ℓ Q)
private theorem unit_of_valuation (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ)
    (hq : q≠0) (hv : padicValRat ℓ q=0) : Unit ℓ (q:Padic ℓ) := by
  unfold Unit
  rw [Padic.eq_padicNorm,padicNorm.eq_zpow_of_nonzero hq,hv]
  norm_num
private theorem nonmatching_unit (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (j : ℕ)
    (hj : j%ℓ≠s.val) : Unit ℓ (((j:ℚ)-s:ℚ):Padic ℓ) := by
  have hu:=Port.Li2.nonmatching_rational_unit (p:=ℓ) s.val j s.isLt hj
  exact unit_of_valuation ℓ _ hu.1 hu.2
private theorem kappa_unit (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) : Unit ℓ (kappa n ℓ s) := by
  unfold Unit kappa kappaQ
  push_cast
  rw [norm_div,norm_prod,norm_prod]
  have hn : (∏ i∈(Finset.Icc 1 n).filter (fun i=>i%ℓ≠s.val),‖((i:Padic ℓ)-s)^3‖)=1:=by
    apply Finset.prod_eq_one
    intro i hi
    rw [norm_pow]
    have hu:=nonmatching_unit ℓ s i (Finset.mem_filter.mp hi).2
    have hu' : ‖(i:Padic ℓ)-s‖=1:=by simpa only [Unit,Rat.cast_sub,Rat.cast_natCast] using hu
    rw [hu']
    norm_num
  have hd : (∏ j∈(Finset.Icc 1 (4*n)).filter (fun j=>j%ℓ≠s.val),‖(j:Padic ℓ)-s‖)=1:=by
    apply Finset.prod_eq_one
    intro j hj
    simpa only [Unit,Rat.cast_sub,Rat.cast_natCast] using nonmatching_unit ℓ s j (Finset.mem_filter.mp hj).2
  rw [hn,hd]
  norm_num
private def crtTailInt (n ℓ : ℕ) (s : Fin ℓ) (P : Ix n ℓ) : ℤ[X]:=
  if s=P.1 then crtPiInt n ℓ s else
    (X+C (P.1.val:ℤ))^P.2.val*
      ∏ t∈(Finset.univ.erase P.1).erase s,(X+C (t.val:ℤ))^(m n ℓ t)
private theorem crtEInt_factor (n ℓ : ℕ) (s : Fin ℓ) (P : Ix n ℓ) :
    crtEInt n ℓ P=(X+C (s.val:ℤ))^(d n ℓ s P)*crtTailInt n ℓ s P := by
  classical
  by_cases hs : s=P.1
  · subst s
    simp only [crtEInt,crtTailInt,d,if_pos rfl,ite_true]
  · have hm : s∈Finset.univ.erase P.1:=by simp [hs]
    have hp : (∏ t∈Finset.univ.erase P.1,(X+C (t.val:ℤ))^(m n ℓ t))=
        (X+C (s.val:ℤ))^(m n ℓ s)*
          ∏ t∈(Finset.univ.erase P.1).erase s,(X+C (t.val:ℤ))^(m n ℓ t):=
      (Finset.mul_prod_erase (Finset.univ.erase P.1)
        (fun t : Fin ℓ=>(X+C (t.val:ℤ))^(m n ℓ t)) hm).symm
    rw [crtEInt,crtPiInt,hp]
    simp only [crtTailInt,d,if_neg hs]
    ring
private theorem crt_pair_quotient (n ℓ : ℕ) (s : Fin ℓ) (P Q : Ix n ℓ) :
    crtE n ℓ P*crtE n ℓ Q /ₘ (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)=
      (crtTailInt n ℓ s P*crtTailInt n ℓ s Q).map (Int.castRingHom ℚ) := by
  have hp:=congrArg (Polynomial.map (Int.castRingHom ℚ)) (crtEInt_factor n ℓ s P)
  have hq:=congrArg (Polynomial.map (Int.castRingHom ℚ)) (crtEInt_factor n ℓ s Q)
  simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_X,
    Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast] at hp hq
  rw [crtE,crtE,hp,hq]
  have he : (X+C (s:ℚ))^(d n ℓ s P)*(crtTailInt n ℓ s P).map (Int.castRingHom ℚ)*
      ((X+C (s:ℚ))^(d n ℓ s Q)*(crtTailInt n ℓ s Q).map (Int.castRingHom ℚ))=
      (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)*
        ((crtTailInt n ℓ s P*crtTailInt n ℓ s Q).map (Int.castRingHom ℚ)) := by
    rw [pow_add,Polynomial.map_mul]
    ring
  rw [he]
  exact Polynomial.mul_divByMonic_cancel_left _ ((monic_X_add_C _).pow _)

private theorem crt_linear_unit (ℓ : ℕ) [Fact ℓ.Prime] (s t : Fin ℓ) (ht : t≠s) :
    Unit ℓ ((((X+C (t.val:ℤ):ℤ[X]).eval (-(s.val:ℤ))):ℤ):Padic ℓ) := by
  have hu:=nonmatching_unit ℓ s t.val (by
    rw [Nat.mod_eq_of_lt t.isLt]
    exact fun h=>ht (Fin.ext h))
  simpa only [Unit,eval_add,eval_X,eval_C,Int.cast_add,Int.cast_neg,Int.cast_natCast,
    Rat.cast_sub,Rat.cast_natCast,sub_eq_add_neg,add_comm] using! hu
private theorem crt_product_unit (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ)
    (S : Finset (Fin ℓ)) (hS : ∀t∈S,t≠s) :
    Unit ℓ ((((∏ t∈S,(X+C (t.val:ℤ))^(m n ℓ t):ℤ[X]).eval (-(s.val:ℤ))):ℤ):Padic ℓ) := by
  unfold Unit
  simp only [eval_prod,eval_pow,Int.cast_prod,Int.cast_pow,norm_prod,norm_pow]
  apply Finset.prod_eq_one
  intro t ht
  have hu:=crt_linear_unit ℓ s t (hS t ht)
  change ‖(((X+C (t.val:ℤ):ℤ[X]).eval (-(s.val:ℤ)):ℤ):Padic ℓ)‖=1 at hu
  rw [hu]
  simp
private theorem crtTailInt_unit (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P : Ix n ℓ) :
    Unit ℓ (((crtTailInt n ℓ s P).eval (-(s.val:ℤ)):ℤ):Padic ℓ) := by
  classical
  unfold crtTailInt
  split_ifs with hs
  · unfold crtPiInt
    exact crt_product_unit n ℓ s _ (fun t ht=> (Finset.mem_erase.mp ht).1)
  · unfold Unit
    rw [eval_mul,eval_pow,Int.cast_mul,Int.cast_pow,norm_mul,norm_pow]
    have hu:=crt_linear_unit ℓ s P.1 (Ne.symm hs)
    have hv:=crt_product_unit n ℓ s ((Finset.univ.erase P.1).erase s)
      (fun t ht=>(Finset.mem_erase.mp ht).1)
    change ‖(((X+C (P.1.val:ℤ):ℤ[X]).eval (-(s.val:ℤ)):ℤ):Padic ℓ)‖=1 at hu
    rw [hu]
    simpa only [Unit,one_pow,one_mul] using hv
private theorem crt_pair_constant_unit (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P Q : Ix n ℓ) :
    Unit ℓ (((crtE n ℓ P*crtE n ℓ Q /ₘ
      (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)).eval (-(s:ℚ)):ℚ):Padic ℓ) := by
  rw [crt_pair_quotient]
  have he : -(s:ℚ)=((-(s.val:ℤ):ℤ):ℚ):=by simp
  rw [he,Polynomial.eval_intCast_map]
  simp only [Int.coe_castRingHom,Rat.cast_intCast,eval_mul,Int.cast_mul]
  unfold Unit
  push_cast
  rw [norm_mul]
  have hp:=crtTailInt_unit n ℓ s P
  have hq:=crtTailInt_unit n ℓ s Q
  change ‖(((crtTailInt n ℓ s P).eval (-(s.val:ℤ)):ℤ):Padic ℓ)‖=1 at hp
  change ‖(((crtTailInt n ℓ s Q).eval (-(s.val:ℤ)):ℤ):Padic ℓ)‖=1 at hq
  simpa using! congrArg₂ (fun a b : ℝ=>a*b) hp hq

private def polyHahn (ℓ : ℕ) [Fact ℓ.Prime] : (Padic ℓ)[X]→+*HahnSeries ℤ (Padic ℓ):=
  (HahnSeries.ofPowerSeries ℤ (Padic ℓ)).comp Polynomial.coeToPowerSeries.ringHom
private theorem polyHahn_injective (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective (polyHahn ℓ) :=
  HahnSeries.ofPowerSeries_injective.comp (Polynomial.coe_injective (Padic ℓ))
private theorem polyHahn_X (ℓ : ℕ) [Fact ℓ.Prime] : polyHahn ℓ X=hX := by
  simp only [polyHahn,RingHom.comp_apply,Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X,HahnSeries.ofPowerSeries_X,hX]
private theorem polyHahn_C (ℓ : ℕ) [Fact ℓ.Prime] (a : Padic ℓ) :
    polyHahn ℓ (C a)=HahnSeries.C a := by
  simp only [polyHahn,RingHom.comp_apply,Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C,HahnSeries.ofPowerSeries_C]
private def affinePolyHahn (ℓ : ℕ) [Fact ℓ.Prime] (a b : ℚ) :
    ℚ[X]→+*HahnSeries ℤ (Padic ℓ):=
  ((polyHahn ℓ).comp (Polynomial.mapRingHom (Rat.castHom (Padic ℓ)))).comp
    (Polynomial.compRingHom (C b*X+C a))
private theorem affinePolyHahn_injective (ℓ : ℕ) [Fact ℓ.Prime] (a b : ℚ) (hb : b≠0) :
    Function.Injective (affinePolyHahn ℓ a b) := by
  have hc : Function.Injective (fun P : ℚ[X]=>P.comp (C b*X+C a)):=by
    intro P Q h
    have he : (C b*X+C a).comp (C b⁻¹*(X-C a))=X := by
      simp only [add_comp,mul_comp,C_comp,X_comp]
      rw [←mul_assoc,←map_mul,mul_inv_cancel₀ hb,map_one,one_mul]
      ring
    have hh:=congrArg (fun R : ℚ[X]=>R.comp (C b⁻¹*(X-C a))) h
    simpa only [comp_assoc,he,comp_X] using hh
  exact (polyHahn_injective ℓ).comp
    ((Polynomial.map_injective (Rat.castHom (Padic ℓ)) (Rat.castHom (Padic ℓ)).injective).comp hc)
private theorem affinePolyHahn_eq (ℓ : ℕ) [Fact ℓ.Prime] (a b : ℚ) :
    affinePolyHahn ℓ a b=Polynomial.eval₂RingHom (algebraMap ℚ (HahnSeries ℤ (Padic ℓ)))
      (HahnSeries.C (b:Padic ℓ)*hX+HahnSeries.C (a:Padic ℓ)) := by
  apply Polynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · simp only [affinePolyHahn,RingHom.comp_apply,Polynomial.coe_compRingHom_apply,
      Polynomial.coe_mapRingHom,Polynomial.X_comp,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
      map_add,map_mul,polyHahn_C,polyHahn_X,eq_ratCast]
private def affineRFHahn (ℓ : ℕ) [Fact ℓ.Prime] (a b : ℚ) (hb : b≠0) :
    RatFunc ℚ→+*HahnSeries ℤ (Padic ℓ):=
  RatFunc.liftRingHom (affinePolyHahn ℓ a b) (by
    intro P hP
    change affinePolyHahn ℓ a b P∈(HahnSeries ℤ (Padic ℓ))⁰
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hz
    have he : P=0:=(affinePolyHahn_injective ℓ a b hb) (by simpa using hz)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hP) he)
private theorem expandRF_affine (ℓ : ℕ) [Fact ℓ.Prime] (a b : ℚ) (hb : b≠0) (F : RatFunc ℚ) :
    expandRF F (HahnSeries.C (b:Padic ℓ)*hX+HahnSeries.C (a:Padic ℓ))=
      affineRFHahn ℓ a b hb F := by
  rw [affineRFHahn,RatFunc.liftRingHom_apply,affinePolyHahn_eq]
  rfl
private theorem atLocal_eq_hom (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (F : RatFunc ℚ) :
    atLocal F ℓ s=affineRFHahn ℓ (-(s:ℚ)) (ℓ:ℚ)
      (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero) F := by
  unfold atLocal
  have he:=expandRF_affine ℓ (-(s:ℚ)) (ℓ:ℚ)
    (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero) F
  simpa only [HahnSeries.C_apply,Rat.cast_neg,Rat.cast_natCast,add_comm] using he
private theorem atZeroPadic_eq_hom (ℓ : ℕ) [Fact ℓ.Prime] (F : RatFunc ℚ) :
    atZeroPadic ℓ F=affineRFHahn ℓ 0 1 one_ne_zero F := by
  unfold atZeroPadic
  have he:=expandRF_affine ℓ 0 1 one_ne_zero F
  simpa only [Rat.cast_zero,Rat.cast_one,map_zero,map_one,one_mul,add_zero] using he
private theorem affineRFHahn_poly (ℓ : ℕ) [Fact ℓ.Prime] (a b : ℚ) (hb : b≠0) (P : ℚ[X]) :
    affineRFHahn ℓ a b hb (rfPoly P)=
      polyHahn ℓ ((P.comp (C b*X+C a)).map (Rat.castHom (Padic ℓ))) := by
  simp only [affineRFHahn,rfPoly,RatFunc.liftRingHom_algebraMap,affinePolyHahn,
    RingHom.comp_apply,Polynomial.coe_compRingHom_apply,Polynomial.coe_mapRingHom]
private theorem atLocal_mul (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (F G : RatFunc ℚ) :
    atLocal (F*G) ℓ s=atLocal F ℓ s*atLocal G ℓ s := by
  simp only [atLocal_eq_hom,map_mul]
private theorem atZeroPadic_mul (ℓ : ℕ) [Fact ℓ.Prime] (F G : RatFunc ℚ) :
    atZeroPadic ℓ (F*G)=atZeroPadic ℓ F*atZeroPadic ℓ G := by
  simp only [atZeroPadic_eq_hom,map_mul]
private theorem germSeries_rescale (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) :
    germSeries ℓ H=HahnSeries.ofPowerSeries ℤ (Padic ℓ)
      (PowerSeries.rescale (ℓ:Padic ℓ)
        (PowerSeries.map PadicInt.Coe.ringHom (PowerSeries.mk H))) := by
  unfold germSeries
  congr 1
  apply PowerSeries.ext
  intro j
  simp only [PowerSeries.coeff_mk,PowerSeries.coeff_rescale,PowerSeries.coeff_map,
    PadicInt.Coe.ringHom_apply]
  ring

private def integralHahnHom (ℓ : ℕ) [Fact ℓ.Prime] :
    PowerSeries (PadicInt ℓ)→+*HahnSeries ℤ (Padic ℓ):=
  (HahnSeries.ofPowerSeries ℤ (Padic ℓ)).comp (PowerSeries.map PadicInt.Coe.ringHom)
private theorem integralHahnHom_injective (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective (integralHahnHom ℓ) := by
  intro f g h
  have he : PowerSeries.map (PadicInt.Coe.ringHom : PadicInt ℓ→+*Padic ℓ) f=
      PowerSeries.map PadicInt.Coe.ringHom g :=
    (HahnSeries.ofPowerSeries_injective (Γ:=ℤ) (R:=Padic ℓ)) h
  exact PowerSeries.map_injective PadicInt.Coe.ringHom Subtype.coe_injective he
private theorem integralHahnHom_C (ℓ : ℕ) [Fact ℓ.Prime] (a : PadicInt ℓ) :
    integralHahnHom ℓ (PowerSeries.C a)=HahnSeries.C (a:Padic ℓ) := by
  simp only [integralHahnHom,RingHom.comp_apply,PowerSeries.map_C,HahnSeries.ofPowerSeries_C,
    PadicInt.Coe.ringHom_apply]
private theorem integralHahnHom_X (ℓ : ℕ) [Fact ℓ.Prime] :
    integralHahnHom ℓ PowerSeries.X=hX := by
  simp only [integralHahnHom,RingHom.comp_apply,PowerSeries.map_X,HahnSeries.ofPowerSeries_X,hX]
private theorem integralHahnHom_poly (ℓ : ℕ) [Fact ℓ.Prime] (P : (PadicInt ℓ)[X]) :
    integralHahnHom ℓ (P:PowerSeries (PadicInt ℓ))=polyHahn ℓ (P.map PadicInt.Coe.ringHom) := by
  unfold integralHahnHom polyHahn
  simp only [RingHom.comp_apply,Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.polynomial_map_coe]
private theorem atZero_poly_value (ℓ : ℕ) [Fact ℓ.Prime] (P : ℚ[X]) :
    atZeroPadic ℓ (rfPoly P)=polyHahn ℓ (P.map (Rat.castHom (Padic ℓ))) := by
  rw [atZeroPadic_eq_hom,affineRFHahn_poly]
  simp only [C_1,C_0,one_mul,add_zero,comp_X]
private theorem integralHahnHom_integer (ℓ : ℕ) [Fact ℓ.Prime] (P : ℤ[X]) :
    integralHahnHom ℓ (P.map (Int.castRingHom (PadicInt ℓ)):PowerSeries (PadicInt ℓ))=
      atZeroPadic ℓ (rfPoly (P.map (Int.castRingHom ℚ))) := by
  rw [integralHahnHom_poly,atZero_poly_value,Polynomial.map_map,Polynomial.map_map]
  congr 2

private theorem atZero_add (ℓ : ℕ) [Fact ℓ.Prime] (F G : RatFunc ℚ) :
    atZeroPadic ℓ (F+G)=atZeroPadic ℓ F+atZeroPadic ℓ G := by
  simp only [atZeroPadic_eq_hom,map_add]
private theorem atZero_sum (ℓ : ℕ) [Fact ℓ.Prime] (f : Fin ℓ→RatFunc ℚ) :
    atZeroPadic ℓ (∑m,f m)=∑m,atZeroPadic ℓ (f m) := by
  simp only [atZeroPadic_eq_hom,map_sum]
private theorem atZero_div (ℓ : ℕ) [Fact ℓ.Prime] (F G : RatFunc ℚ) :
    atZeroPadic ℓ (F/G)=atZeroPadic ℓ F/atZeroPadic ℓ G := by
  simp only [atZeroPadic_eq_hom,map_div₀]
private theorem pole_rep_cleared (ℓ : ℕ) [Fact ℓ.Prime] (F : RatFunc ℚ) (Q : ℤ[X])
    (r : Fin ℓ→ℚ) (hr : ∀m,Intg ℓ (r m:Padic ℓ))
    (hF : F=rfPoly (Q.map (Int.castRingHom ℚ))+
      ∑ m : Fin ℓ,rfPoly (C (r m))/rfPoly (X+C (m:ℚ))) :
    let centers:=Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)
    let rI : Fin ℓ→PadicInt ℓ:=fun m=>⟨(r m:Padic ℓ),hr m⟩
    let f : PowerSeries (PadicInt ℓ):=(Q.map (Int.castRingHom (PadicInt ℓ)):PowerSeries (PadicInt ℓ))
    atZeroPadic ℓ F*integralHahnHom ℓ (Port.Li2.integralPoleDenominator centers : PowerSeries (PadicInt ℓ))=
      integralHahnHom ℓ (Port.Li2.integralPoleNumerator centers f rI) := by
  classical
  let centers:=Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)
  let rI : Fin ℓ→PadicInt ℓ:=fun m=>⟨(r m:Padic ℓ),hr m⟩
  let f : PowerSeries (PadicInt ℓ):=(Q.map (Int.castRingHom (PadicInt ℓ)):PowerSeries (PadicInt ℓ))
  let D : HahnSeries ℤ (Padic ℓ):=integralHahnHom ℓ
    (Port.Li2.integralPoleDenominator centers : PowerSeries (PadicInt ℓ))
  let C : Fin ℓ→HahnSeries ℤ (Padic ℓ):=fun m=>integralHahnHom ℓ
    (Port.Li2.integralPoleCofactor centers m : PowerSeries (PadicInt ℓ))
  let l : Fin ℓ→HahnSeries ℤ (Padic ℓ):=fun m=>hX-HahnSeries.C ((centers m:PadicInt ℓ):Padic ℓ)
  have hl (m : Fin ℓ) : l m≠0:=by
    have he:=(polyHahn_injective ℓ).ne (Polynomial.X_sub_C_ne_zero ((centers m:PadicInt ℓ):Padic ℓ))
    simpa only [l,map_sub,polyHahn_X,polyHahn_C,map_zero] using he
  have hD (m : Fin ℓ) : D=l m*C m:=by
    dsimp only [D,C,l]
    rw [Port.Li2.integralPoleDenominator_factor centers m,Polynomial.coe_mul,
      Polynomial.coe_sub,Polynomial.coe_X,Polynomial.coe_C,map_mul,map_sub,
      integralHahnHom_X,integralHahnHom_C]
  have hval : atZeroPadic ℓ F=integralHahnHom ℓ f+
      ∑m : Fin ℓ,HahnSeries.C ((rI m:PadicInt ℓ):Padic ℓ)/l m := by
    rw [hF,atZero_add,atZero_sum,←integralHahnHom_integer]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [atZero_div]
    rw [atZero_poly_value,atZero_poly_value,Polynomial.map_C,Polynomial.map_add,
      Polynomial.map_X,Polynomial.map_C,map_add,polyHahn_X,polyHahn_C,polyHahn_C]
    simp only [l,centers,rI,Port.Unified.Proofs.Hermite.generalPoleCenters,
      PadicInt.coe_neg,PadicInt.coe_natCast,map_neg,sub_neg_eq_add,eq_ratCast,Rat.cast_natCast]
  have hnum : integralHahnHom ℓ (Port.Li2.integralPoleNumerator centers f rI)=
      D*integralHahnHom ℓ f+∑ m : Fin ℓ,HahnSeries.C ((rI m:PadicInt ℓ):Padic ℓ)*C m := by
    simp only [Port.Li2.integralPoleNumerator,map_add,map_mul,
      Port.Li2.polynomial_coe_finset_sum,map_sum,Polynomial.coe_mul,Polynomial.coe_C,
      integralHahnHom_C,D,C]
  change atZeroPadic ℓ F*D=_
  rw [hval,add_mul,Finset.sum_mul,hnum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro m hm
    rw [hD m]
    field_simp [hl m]

private theorem denominator_derivative (S : Finset ℕ) (m : ℕ) (hm : m∈S) :
    (poleProd S).derivative.eval (-(m:ℚ))=∏ n∈S.erase m,((n:ℚ)-m) := by
  classical
  have hp : poleProd S=(X+C (m:ℚ))*poleProd (S.erase m) :=
    (Finset.mul_prod_erase S (fun m : ℕ=>X+C (m:ℚ)) hm).symm
  rw [hp]
  simp [poleProd,derivative_mul,eval_prod,sub_eq_add_neg,add_comm]
private theorem integer_poleCoeff_integral (ℓ : ℕ) [Fact ℓ.Prime]
    (P : ℤ[X]) (S : Finset ℕ) (hS : ∀ m∈S,m<ℓ) (m : ℕ) (hm : m∈S) :
    Intg ℓ (poleCoeff (P.map (Int.castRingHom ℚ)) S m:Padic ℓ) := by
  classical
  have hn : ‖(((P.map (Int.castRingHom ℚ)).eval (-(m:ℚ)):ℚ):Padic ℓ)‖≤1:=by
    rw [show -(m:ℚ)=((-(m:ℤ):ℤ):ℚ) by simp,Polynomial.eval_intCast_map]
    simpa using!
      PadicInt.norm_le_one ((P.eval (-(m:ℤ)):ℤ):PadicInt ℓ)
  have hd : ‖((∏ n∈S.erase m,((n:ℚ)-m):ℚ):Padic ℓ)‖=1 := by
    push_cast
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro n hn
    have hni:=Finset.mem_erase.mp hn
    have hnon : ¬(ℓ:ℤ)∣(n:ℤ)-m:=by
      intro he
      have hEq : (n:ℤ)%(ℓ:ℤ)=(m:ℤ)%(ℓ:ℤ):=
        Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd he)
      rw [←Int.natCast_mod,←Int.natCast_mod,
        Nat.mod_eq_of_lt (hS n hni.2),Nat.mod_eq_of_lt (hS m hm),Int.natCast_inj] at hEq
      exact hni.1 hEq
    have hu : ‖(((n:ℤ)-m:ℤ):PadicInt ℓ)‖=1:=le_antisymm (PadicInt.norm_le_one _)
      (le_of_not_gt (by rwa [PadicInt.norm_int_lt_one_iff_dvd]))
    simpa using! hu
  unfold Intg poleCoeff
  rw [denominator_derivative S m hm,Rat.cast_div,norm_div,hd,div_one]
  exact hn
private theorem integer_quotient_coeff_integral (ℓ : ℕ) [Fact ℓ.Prime]
    (P : ℤ[X]) (S : Finset ℕ) (i : ℕ) :
    Intg ℓ (((P.map (Int.castRingHom ℚ) /ₘ poleProd S).coeff i):Padic ℓ) := by
  classical
  let D : ℤ[X]:=∏ m∈S,(X+C (m:ℤ))
  have hD : D.Monic:=Polynomial.monic_prod_of_monic _ _ (fun m hm=>monic_X_add_C _)
  have hmap : D.map (Int.castRingHom ℚ)=poleProd S:=by
    simp only [D,poleProd,Polynomial.map_prod,Polynomial.map_add,Polynomial.map_X,
      Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast]
  rw [←hmap,←Polynomial.map_divByMonic _ hD,Polynomial.coeff_map]
  simpa only [Int.coe_castRingHom,Int.cast_natCast,Rat.cast_intCast,
    Intg,PadicInt.norm_def,PadicInt.coe_intCast] using PadicInt.norm_le_one ((P /ₘ D).coeff i:PadicInt ℓ)

private theorem integer_simple_poles (ℓ : ℕ) [Fact ℓ.Prime]
    (P : ℤ[X]) (S : Finset ℕ) (hS : ∀m∈S,m<ℓ) :
    ∃ Q : ℤ[X],∃ r : Fin ℓ→ℚ,
      (∀m,Intg ℓ (r m:Padic ℓ)) ∧
      rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S)=
        rfPoly (Q.map (Int.castRingHom ℚ))+
          ∑ m : Fin ℓ,rfPoly (C (r m))/rfPoly (X+C (m:ℚ)) := by
  classical
  let D : ℤ[X]:=∏ m∈S,(X+C (m:ℤ))
  let Q : ℤ[X]:=P /ₘ D
  have hD : D.Monic:=Polynomial.monic_prod_of_monic _ _ (fun m hm=>monic_X_add_C _)
  have hmap : D.map (Int.castRingHom ℚ)=poleProd S:=by
    simp only [D,poleProd,Polynomial.map_prod,Polynomial.map_add,Polynomial.map_X,
      Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast]
  have hQ : Q.map (Int.castRingHom ℚ)=P.map (Int.castRingHom ℚ) /ₘ poleProd S:=by
    rw [←hmap]
    exact Polynomial.map_divByMonic _ hD
  let r : Fin ℓ→ℚ:=fun m=>if m.val∈S then poleCoeff (P.map (Int.castRingHom ℚ)) S m else 0
  refine ⟨Q,r,?_,?_⟩
  · intro m
    dsimp only [r]
    split_ifs with hm
    · exact integer_poleCoeff_integral ℓ P S hS m hm
    · simp [Intg]
  · have he:=pole_fraction_decomposition (P.map (Int.castRingHom ℚ)) S
    rw [←hQ] at he
    rw [he]
    congr 1
    let f : ℕ→RatFunc ℚ:=fun m=>rfPoly (C (if m∈S then poleCoeff (P.map (Int.castRingHom ℚ)) S m else 0))/
      rfPoly (X+C (m:ℚ))
    have hs : S⊆Finset.range ℓ:=by intro m hm;exact Finset.mem_range.mpr (hS m hm)
    have hpad : (∑ m∈S,rfPoly (C (poleCoeff (P.map (Int.castRingHom ℚ)) S m))/rfPoly (X+C (m:ℚ)))=
        ∑ m∈Finset.range ℓ,f m := by
      calc
        _=∑ m∈S,f m:=by
          apply Finset.sum_congr rfl
          intro m hm
          simp only [f,if_pos hm]
        _=_:=Finset.sum_subset hs (fun m hm hn=>by simp [f,hn,rfPoly])
    rw [←Fin.sum_univ_eq_sum_range] at hpad
    exact hpad
private def classBaseNumerator (n ℓ : ℕ) (s : Fin ℓ) (d : ℕ) : ℤ[X]:=
  X^d * if s.val=0 then ∏k∈Finset.Icc 1 (a n ℓ s),(X+C (k:ℤ))^2
    else ∏k∈Finset.range (a n ℓ s),(X+C (k:ℤ))^2
private theorem classBase_fraction (n ℓ : ℕ) (s : Fin ℓ) (d : ℕ) :
    rfX^d*classWeight n ℓ s=
      rfPoly ((classBaseNumerator n ℓ s d).map (Int.castRingHom ℚ))/
        rfPoly (poleProd (poleSet (classKey n ℓ s))) := by
  have hx : (rfX:RatFunc ℚ)≠0:=RatFunc.algebraMap_ne_zero (by simp)
  by_cases hs : s.val=0
  · simp only [classWeight,hs,ite_true,weight,weightNum,classKey,weightDen,poleProd,
      classBaseNumerator,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,
      Polynomial.map_prod,Polynomial.map_add,Polynomial.map_C,Int.coe_castRingHom,
      Int.cast_natCast]
    unfold rfX rfPoly at *
    simp only [map_mul,map_pow]
    field_simp [hx] <;> ring
  · simp only [classWeight,hs,ite_false,weight,weightNum,classKey,weightDen,poleProd,
      classBaseNumerator,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,
      Polynomial.map_prod,Polynomial.map_add,Polynomial.map_C,Int.coe_castRingHom,
      Int.cast_natCast]
    unfold rfX rfPoly at *
    simp only [map_mul,map_pow]
    ring
private theorem classBase_simple_poles (n ℓ : ℕ) [Fact ℓ.Prime]
    (hR : Range n ℓ) (s : Fin ℓ) (d : ℕ) :
    ∃ Q : ℤ[X],∃ r : Fin ℓ→ℚ,
      (∀m,Intg ℓ (r m:Padic ℓ)) ∧
      rfX^d*classWeight n ℓ s=rfPoly (Q.map (Int.castRingHom ℚ))+
        ∑ m : Fin ℓ,rfPoly (C (r m))/rfPoly (X+C (m:ℚ)) := by
  rw [classBase_fraction]
  apply integer_simple_poles
  intro m hm
  have hc:=(class_counts n ℓ hR).1 s
  have hp:=(Fact.out : ℓ.Prime).pos
  have hlt : c n ℓ s<ℓ:=by omega
  unfold poleSet classKey at hm
  split_ifs at hm with hs
  · have he:=Finset.mem_Ioc.mp hm
    dsimp only at he
    omega
  · have he:=Finset.mem_Ico.mp hm
    dsimp only at he
    omega

private theorem class_multiplier_cleared (n ℓ : ℕ) [Fact ℓ.Prime]
    (hR : Range n ℓ) (s : Fin ℓ) (d : ℕ)
    (g : PowerSeries (PadicInt ℓ)) (hg : PowerSeries.IsRestricted 1 g) :
    ∃ f : PowerSeries (PadicInt ℓ),∃ r : Fin ℓ→PadicInt ℓ,
      PowerSeries.IsRestricted 1 f ∧
      (integralHahnHom ℓ g*atZeroPadic ℓ (rfX^d*classWeight n ℓ s))*
        integralHahnHom ℓ (Port.Li2.integralPoleDenominator
          (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)):PowerSeries (PadicInt ℓ))=
        integralHahnHom ℓ (Port.Li2.integralPoleNumerator
          (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)) f r) := by
  classical
  obtain ⟨Q,r,hr,he⟩:=classBase_simple_poles n ℓ hR s d
  let centers:=Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)
  let rI : Fin ℓ→PadicInt ℓ:=fun m=>⟨(r m:Padic ℓ),hr m⟩
  let f : PowerSeries (PadicInt ℓ):=(Q.map (Int.castRingHom (PadicInt ℓ)):PowerSeries (PadicInt ℓ))
  refine ⟨Port.Li2.integralPoleMulRegular centers g f rI,
    Port.Li2.integralPoleMulResidue centers g rI,?_,?_⟩
  · apply Port.Li2.integralPoleMulRegular_isRestricted centers g f hg
    exact Port.Li2.polynomial_isRestricted _
  · have hp:=pole_rep_cleared ℓ (rfX^d*classWeight n ℓ s) Q r hr he
    change atZeroPadic ℓ (rfX^d*classWeight n ℓ s)*
      integralHahnHom ℓ (Port.Li2.integralPoleDenominator centers:PowerSeries (PadicInt ℓ))=
        integralHahnHom ℓ (Port.Li2.integralPoleNumerator centers f rI) at hp
    rw [Port.Li2.integralPoleNumerator_mul centers g f hg rI,map_mul,←hp]
    ring
private theorem parameterV_formula (z : ℚ) (hz : z≠1) (P : ℚ[X]) :
    Port.Li2.parameterV z P=
      ∑i∈Finset.Icc 1 P.natDegree,(i:ℚ)*P.coeff i*liNeg (i-1) z := by
  let f : ℕ→ℚ→ℚ:=fun i a=>(i:ℚ)*a*liNeg (i-1) z
  have hpoly : ∀P : ℚ[X],Port.Li2.parameterG z P.derivative=P.sum f := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ=>
      rw [derivative_add,Port.Li2.parameterG_add,hP,hQ]
      symm
      exact Polynomial.sum_add_index _ _ _ (fun i=>by simp [f]) (fun i a b=>by dsimp [f];ring)
    | monomial i a=>
      rw [Polynomial.sum_monomial_index a f (by simp [f])]
      cases i with
      | zero=>simp [f,Port.Li2.parameterG]
      | succ i=>
        simp only [derivative_monomial_succ,Port.Li2.parameterG_monomial]
        dsimp only [f]
        rw [liNeg_eq_parameterMoment z hz]
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
  unfold Port.Li2.parameterV
  rw [hpoly,Polynomial.sum_over_range P (f:=f) (fun i=>by simp [f])]
  symm
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr (by have he:=Finset.mem_Icc.mp hi;omega)
  · intro i hi hn
    have he:=Finset.mem_range.mp hi
    have hz : i=0:=by
      by_contra h
      apply hn
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    simp [hz,f]
private theorem canonical_functional (ℓ : ℕ) [Fact ℓ.Prime] (P : ℚ[X]) (S : Finset ℕ)
    (φ : ℚ[X]→Padic ℓ) (ψ : ℕ→Padic ℓ) :
    let F:=rfPoly P/rfPoly (poleProd S)
    φ (pp F)+(∑ m∈poleIndices F,(poleRes F m:Padic ℓ)*ψ m)=
      φ (P /ₘ poleProd S)+∑ m∈S,(poleCoeff P S m:Padic ℓ)*ψ m := by
  classical
  let F:=rfPoly P/rfPoly (poleProd S)
  have hc:=fraction_coefficients P S
  have hdiv : F.denom∣poleProd S:=RatFunc.denom_div_dvd P (poleProd S)
  obtain ⟨hD,hI⟩:=canonical_poles F S hdiv
  have hsub : poleIndices F⊆S:=by rw [hI];exact Finset.filter_subset _ _
  change φ (pp F)+(∑ m∈poleIndices F,(poleRes F m:Padic ℓ)*ψ m)=
    φ (P /ₘ poleProd S)+∑ m∈S,(poleCoeff P S m:Padic ℓ)*ψ m
  rw [hc.1]
  congr 1
  let f : ℕ→Padic ℓ:=fun m=>((if m∈poleIndices F then poleRes F m else 0:ℚ):Padic ℓ)*ψ m
  calc
    (∑ m∈poleIndices F,(poleRes F m:Padic ℓ)*ψ m)=∑ m∈poleIndices F,f m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [f,if_pos hm]
    _=∑ m∈S,f m:=Finset.sum_subset hsub (fun m hmS hmI=>by simp [f,hmI])
    _=∑ m∈S,(poleCoeff P S m:Padic ℓ)*ψ m := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp only [f]
      rw [hc.2 m hm]


private theorem localV_fraction (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] (hw : z^ℓ≠1)
    (ξ : Padic ℓ) (P : ℚ[X]) (S : Finset ℕ) :
    localV z ℓ ξ (rfPoly P/rfPoly (poleProd S))=
      (Port.Li2.parameterV (z^ℓ) (P /ₘ poleProd S):ℚ)+
      ∑m∈S,(poleCoeff P S m:Padic ℓ)*
        (-(z:Padic ℓ)^(-((ℓ*m:ℕ):ℤ))*((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) m:ℚ))) := by
  classical
  let F:=rfPoly P/rfPoly (poleProd S)
  have hP:=congrArg (fun q : ℚ=>(q:Padic ℓ)) (parameterV_formula (z^ℓ) hw (pp F))
  simp only [Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast] at hP
  change localV z ℓ ξ F=_
  unfold localV
  rw [←hP,sub_eq_add_neg,←Finset.sum_neg_distrib]
  have hc:=canonical_functional ℓ P S
    (fun Q=>(Port.Li2.parameterV (z^ℓ) Q:ℚ))
    (fun m=>-(z:Padic ℓ)^(-((ℓ*m:ℕ):ℤ))*((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) m:ℚ)))
  simpa only [F,mul_neg,neg_mul,mul_assoc] using hc

private theorem localV_integral_operator (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hu : z^ℓ≠0∧padicValRat ℓ (z^ℓ)=0) (hreg : Port.Li2.VG ℓ (z^ℓ/(1-z^ℓ)) 0)
    (hw : z^ℓ≠1) (ξ : Padic ℓ) (P : ℚ[X]) (S : Finset ℕ)
    (hS : ∀m∈S,m<ℓ) (Q : ℤ[X])
    (hQ : Q.map (Int.castRingHom ℚ)=P /ₘ poleProd S)
    (hr : ∀m∈S,Intg ℓ (poleCoeff P S m:Padic ℓ)) :
    let rQ : Fin ℓ→ℚ:=fun m=>if m.val∈S then poleCoeff P S m else 0
    let rI : Fin ℓ→PadicInt ℓ:=fun m=>⟨(rQ m:Padic ℓ),by
      dsimp only [rQ];split_ifs with hm
      · exact hr m hm
      · simp [Intg]⟩
    (Port.Unified.Proofs.Hermite.generalPoleV (z^ℓ) hu hreg
      (Q.map (Int.castRingHom (PadicInt ℓ)):PowerSeries (PadicInt ℓ)) rI).eval₂
      (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)=
        localV z ℓ ξ (rfPoly P/rfPoly (poleProd S)) := by
  classical
  intro rQ rI
  have hmap : (Q.map (Int.castRingHom (PadicInt ℓ))).map (algebraMap (PadicInt ℓ) (Padic ℓ))=
      (P /ₘ poleProd S).map (Rat.castHom (Padic ℓ)):=by
    rw [←hQ,Polynomial.map_map,Polynomial.map_map]
    congr 1
  have hp:=Port.Li2.padicParameterV_of_polynomial_map (z^ℓ) hreg
    (Q.map (Int.castRingHom (PadicInt ℓ))) (P /ₘ poleProd S) hmap
  have hval (m : Fin ℓ) :
      (Port.Li2.integralVPole (z^ℓ) hu.1 hu.2 m.val m.isLt).eval₂
        (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)=
      -(z:Padic ℓ)^(-((ℓ*m.val:ℕ):ℤ))*((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) m.val:ℚ)):=by
    have he : ((z^ℓ:ℚ):Padic ℓ)⁻¹^m.val=(z:Padic ℓ)^(-((ℓ*m.val:ℕ):ℤ)):=by
      rw [_root_.zpow_neg,zpow_natCast,Rat.cast_pow,inv_pow,pow_mul]
    simp only [Port.Li2.integralVPole,eval₂_mul,eval₂_C,eval₂_sub,eval₂_X]
    simp only [map_neg,map_mul,PadicInt.algebraMap_apply,
      Port.Li2.integralParameterInvPow,Port.Li2.integralParameterTau,Port.Li2.integralRational]
    simp only [Rat.cast_pow,Rat.cast_inv]
    change -((z^ℓ:ℚ):Padic ℓ)⁻¹^m.val*((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) m.val:ℚ))=_
    rw [he]
  unfold Port.Unified.Proofs.Hermite.generalPoleV Port.Li2.restrictedPoleFunctional
  rw [eval₂_add,eval₂_C,eval₂_finset_sum,localV_fraction z ℓ hw ξ P S]
  change ((Port.Li2.restrictedV (Port.Li2.integralParameterMoment (z^ℓ) hreg)
    (Q.map (Int.castRingHom (PadicInt ℓ)):PowerSeries (PadicInt ℓ)):PadicInt ℓ):Padic ℓ)+_=_
  rw [hp]
  congr 1
  simp_rw [eval₂_mul,eval₂_C,hval]
  let f : ℕ→Padic ℓ:=fun m=>
    ((if m∈S then poleCoeff P S m else 0:ℚ):Padic ℓ)*
      (-(z:Padic ℓ)^(-((ℓ*m:ℕ):ℤ))*((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) m:ℚ)))
  change (∑m : Fin ℓ,f m)=_
  rw [Fin.sum_univ_eq_sum_range]
  symm
  calc
    _=∑m∈S,f m:=by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [f,if_pos hm]
    _=∑m∈Finset.range ℓ,f m:=Finset.sum_subset
      (fun m hm=>Finset.mem_range.mpr (hS m hm)) (fun m hm hn=>by simp [f,hn])
private theorem integer_canonical_poles (ℓ : ℕ) [Fact ℓ.Prime]
    (P : ℤ[X]) (S : Finset ℕ) (hS : ∀m∈S,m<ℓ) :
    ∃ Q : ℤ[X],∃ r : Fin ℓ→ℚ,
      Q.map (Int.castRingHom ℚ)=P.map (Int.castRingHom ℚ) /ₘ poleProd S ∧
      (∀m,r m=if m.val∈S then poleCoeff (P.map (Int.castRingHom ℚ)) S m else 0) ∧
      (∀m,Intg ℓ (r m:Padic ℓ)) ∧
      rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S)=
        rfPoly (Q.map (Int.castRingHom ℚ))+
          ∑ m : Fin ℓ,rfPoly (C (r m))/rfPoly (X+C (m:ℚ)) := by
  classical
  let D : ℤ[X]:=∏ m∈S,(X+C (m:ℤ))
  let Q : ℤ[X]:=P /ₘ D
  have hD : D.Monic:=Polynomial.monic_prod_of_monic _ _ (fun m hm=>monic_X_add_C _)
  have hmap : D.map (Int.castRingHom ℚ)=poleProd S:=by
    simp only [D,poleProd,Polynomial.map_prod,Polynomial.map_add,Polynomial.map_X,
      Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast]
  have hQ : Q.map (Int.castRingHom ℚ)=P.map (Int.castRingHom ℚ) /ₘ poleProd S:=by
    rw [←hmap]
    exact Polynomial.map_divByMonic _ hD
  let r : Fin ℓ→ℚ:=fun m=>if m.val∈S then poleCoeff (P.map (Int.castRingHom ℚ)) S m else 0
  refine ⟨Q,r,hQ,fun m=>rfl,?_,?_⟩
  · intro m
    dsimp only [r]
    split_ifs with hm
    · exact integer_poleCoeff_integral ℓ P S hS m hm
    · simp [Intg]
  · have he:=pole_fraction_decomposition (P.map (Int.castRingHom ℚ)) S
    rw [←hQ] at he
    rw [he]
    congr 1
    let f : ℕ→RatFunc ℚ:=fun m=>rfPoly (C (if m∈S then poleCoeff (P.map (Int.castRingHom ℚ)) S m else 0))/
      rfPoly (X+C (m:ℚ))
    have hs : S⊆Finset.range ℓ:=by intro m hm;exact Finset.mem_range.mpr (hS m hm)
    have hpad : (∑ m∈S,rfPoly (C (poleCoeff (P.map (Int.castRingHom ℚ)) S m))/rfPoly (X+C (m:ℚ)))=
        ∑ m∈Finset.range ℓ,f m := by
      calc
        _=∑ m∈S,f m:=by
          apply Finset.sum_congr rfl
          intro m hm
          simp only [f,if_pos hm]
        _=_:=Finset.sum_subset hs (fun m hm hn=>by simp [f,hn,rfPoly])
    rw [←Fin.sum_univ_eq_sum_range] at hpad
    exact hpad

private theorem localV_of_integral_rep (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hu : z^ℓ≠0∧padicValRat ℓ (z^ℓ)=0) (hreg : Port.Li2.VG ℓ (z^ℓ/(1-z^ℓ)) 0)
    (hw : z^ℓ≠1) (ξ : Padic ℓ) (P : ℤ[X]) (S : Finset ℕ)
    (hS : ∀m∈S,m<ℓ) (f : PowerSeries (PadicInt ℓ))
    (hf : PowerSeries.IsRestricted 1 f) (r : Fin ℓ→PadicInt ℓ)
    (he : atZeroPadic ℓ (rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S))*
      integralHahnHom ℓ (Port.Li2.integralPoleDenominator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)):PowerSeries (PadicInt ℓ))=
      integralHahnHom ℓ (Port.Li2.integralPoleNumerator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)) f r)) :
    (Port.Unified.Proofs.Hermite.generalPoleV (z^ℓ) hu hreg f r).eval₂
      (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)=
      localV z ℓ ξ (rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S)) := by
  classical
  obtain ⟨Q,rQ,hQ,heq,hr,hF⟩:=integer_canonical_poles ℓ P S hS
  have heq' : rQ=(fun m : Fin ℓ=>if m.val∈S then poleCoeff (P.map (Int.castRingHom ℚ)) S m else 0):=funext heq
  subst rQ
  let centers:=Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)
  let rc : Fin ℓ→PadicInt ℓ:=fun m=>⟨((if m.val∈S then poleCoeff (P.map (Int.castRingHom ℚ)) S m else 0:ℚ):Padic ℓ),hr m⟩
  let fc : PowerSeries (PadicInt ℓ):=(Q.map (Int.castRingHom (PadicInt ℓ)):PowerSeries (PadicInt ℓ))
  have hcan:=pole_rep_cleared ℓ _ Q _ hr hF
  change atZeroPadic ℓ (rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S))*
    integralHahnHom ℓ (Port.Li2.integralPoleDenominator centers:PowerSeries (PadicInt ℓ))=
      integralHahnHom ℓ (Port.Li2.integralPoleNumerator centers fc rc) at hcan
  have hn : Port.Li2.integralPoleNumerator centers f r=Port.Li2.integralPoleNumerator centers fc rc:=
    integralHahnHom_injective ℓ (he.symm.trans hcan)
  obtain ⟨hfe,hre⟩:=Port.Li2.integralPoleNumerator_injective centers
    Port.Unified.Proofs.Hermite.generalPoleCenters_injective f fc hf
    (Port.Li2.polynomial_isRestricted _) r rc hn
  rw [hfe,hre]
  exact localV_integral_operator z ℓ hu hreg hw ξ (P.map (Int.castRingHom ℚ)) S hS Q hQ
    (fun m hm=>integer_poleCoeff_integral ℓ P S hS m hm)

private theorem class_poles_lt (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) (s : Fin ℓ) :
    ∀m∈poleSet (classKey n ℓ s),m<ℓ := by
  intro m hm
  have hc:=(class_counts n ℓ hR).1 s
  have hp:=(Fact.out : ℓ.Prime).pos
  unfold poleSet classKey at hm
  split_ifs at hm with hs
  · have he:=Finset.mem_Ioc.mp hm
    dsimp only at he
    omega
  · have he:=Finset.mem_Ico.mp hm
    dsimp only at he
    omega
private theorem classV_of_integral_rep (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hu : z^ℓ≠0∧padicValRat ℓ (z^ℓ)=0) (hreg : Port.Li2.VG ℓ (z^ℓ/(1-z^ℓ)) 0)
    (hw : z^ℓ≠1) (hR : Range n ℓ) (s : Fin ℓ) (ξ : Padic ℓ) (d : ℕ)
    (f : PowerSeries (PadicInt ℓ)) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin ℓ→PadicInt ℓ)
    (he : atZeroPadic ℓ (rfX^d*classWeight n ℓ s)*
      integralHahnHom ℓ (Port.Li2.integralPoleDenominator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)):PowerSeries (PadicInt ℓ))=
      integralHahnHom ℓ (Port.Li2.integralPoleNumerator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)) f r)) :
    (Port.Unified.Proofs.Hermite.generalPoleV (z^ℓ) hu hreg f r).eval₂
      (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)=
      localV z ℓ ξ (rfX^d*classWeight n ℓ s) := by
  rw [classBase_fraction] at he ⊢
  exact localV_of_integral_rep z ℓ hu hreg hw ξ (classBaseNumerator n ℓ s d)
    (poleSet (classKey n ℓ s)) (class_poles_lt n ℓ hR s) f hf r he
private theorem atZero_rfX (ℓ : ℕ) [Fact ℓ.Prime] :
    atZeroPadic ℓ (rfX:RatFunc ℚ)=integralHahnHom ℓ PowerSeries.X := by
  change atZeroPadic ℓ (rfPoly X)=_
  rw [atZero_poly_value,Polynomial.map_X,polyHahn_X,integralHahnHom_X]
private theorem atZero_pow (ℓ : ℕ) [Fact ℓ.Prime] (F : RatFunc ℚ) (j : ℕ) :
    atZeroPadic ℓ (F^j)=atZeroPadic ℓ F^j := by
  simp only [atZeroPadic_eq_hom,map_pow]
private theorem classV_monomial (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hu : z^ℓ≠0∧padicValRat ℓ (z^ℓ)=0) (hreg : Port.Li2.VG ℓ (z^ℓ/(1-z^ℓ)) 0)
    (hw : z^ℓ≠1) (hR : Range n ℓ) (s : Fin ℓ) (ξ : Padic ℓ) (d j : ℕ)
    (f : PowerSeries (PadicInt ℓ)) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin ℓ→PadicInt ℓ)
    (he : atZeroPadic ℓ (rfX^d*classWeight n ℓ s)*
      integralHahnHom ℓ (Port.Li2.integralPoleDenominator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)):PowerSeries (PadicInt ℓ))=
      integralHahnHom ℓ (Port.Li2.integralPoleNumerator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)) f r)) :
    (Port.Unified.Proofs.Hermite.generalPoleV (z^ℓ) hu hreg
      (Port.Li2.integralPoleMulRegular Port.Unified.Proofs.Hermite.generalPoleCenters (PowerSeries.X^j) f r)
      (Port.Li2.integralPoleMulResidue Port.Unified.Proofs.Hermite.generalPoleCenters (PowerSeries.X^j) r)).eval₂
      (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)=
        localV z ℓ ξ (rfX^(d+j)*classWeight n ℓ s) := by
  have hj : PowerSeries.IsRestricted 1 (PowerSeries.X^j:PowerSeries (PadicInt ℓ)):=by
    simpa only [Polynomial.coe_pow,Polynomial.coe_X] using Port.Li2.polynomial_isRestricted ((X:(PadicInt ℓ)[X])^j)
  apply classV_of_integral_rep z n ℓ hu hreg hw hR s ξ (d+j) _
    (Port.Li2.integralPoleMulRegular_isRestricted _ _ _ hj hf _) _
  rw [Port.Li2.integralPoleNumerator_mul _ _ _ hj,map_mul,←he]
  rw [show (rfX:RatFunc ℚ)^(d+j)*classWeight n ℓ s=
    rfX^j*(rfX^d*classWeight n ℓ s) by rw [pow_add];ring,
      atZeroPadic_mul,atZero_pow,atZero_rfX,map_pow]
  ring
variable {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem pole_mul_add (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (g h f : PowerSeries (PadicInt ℓ))
    (hg : PowerSeries.IsRestricted 1 g) (hh : PowerSeries.IsRestricted 1 h)
    (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ) :
    Port.Li2.integralPoleMulRegular c (g+h) f r=
      Port.Li2.integralPoleMulRegular c g f r+Port.Li2.integralPoleMulRegular c h f r ∧
    Port.Li2.integralPoleMulResidue c (g+h) r=
      Port.Li2.integralPoleMulResidue c g r+Port.Li2.integralPoleMulResidue c h r := by
  apply Port.Li2.integralPoleNumerator_injective c hc _ _
    (Port.Li2.integralPoleMulRegular_isRestricted c (g+h) f (PowerSeries.isRestricted.add 1 hg hh) hf r)
    (PowerSeries.isRestricted.add 1
      (Port.Li2.integralPoleMulRegular_isRestricted c g f hg hf r)
      (Port.Li2.integralPoleMulRegular_isRestricted c h f hh hf r))
  rw [Port.Li2.integralPoleNumerator_mul,Port.Li2.integralPoleNumerator_add,
    Port.Li2.integralPoleNumerator_mul,Port.Li2.integralPoleNumerator_mul,add_mul]
  all_goals first | assumption | exact PowerSeries.isRestricted.add 1 hg hh
private theorem pole_mul_smul (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (g f : PowerSeries (PadicInt ℓ))
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : ι→PadicInt ℓ) (a : PadicInt ℓ) :
    Port.Li2.integralPoleMulRegular c (a • g) f r=a • Port.Li2.integralPoleMulRegular c g f r ∧
    Port.Li2.integralPoleMulResidue c (a • g) r=a • Port.Li2.integralPoleMulResidue c g r := by
  apply Port.Li2.integralPoleNumerator_injective c hc _ _
    (Port.Li2.integralPoleMulRegular_isRestricted c (a • g) f
      (Port.Li2.restrictedSeries_smul 1 hg a) hf r)
    (Port.Li2.restrictedSeries_smul 1
      (Port.Li2.integralPoleMulRegular_isRestricted c g f hg hf r) a)
  rw [Port.Li2.integralPoleNumerator_mul,Port.Li2.integralPoleNumerator_smul,
    Port.Li2.integralPoleNumerator_mul]
  rw [Algebra.smul_def]
  change (PowerSeries.C a*g)*_=PowerSeries.C a*(g*_)
  ring
  all_goals first | assumption | exact Port.Li2.restrictedSeries_smul 1 hg a
private def poleMultiplierFunctional (c : ι→PadicInt ℓ) (μ : ℕ→PadicInt ℓ)
    (w : ι→(PadicInt ℓ)[X]) (f : PowerSeries (PadicInt ℓ)) (r : ι→PadicInt ℓ)
    (g : PowerSeries (PadicInt ℓ)) : (PadicInt ℓ)[X]:=
  Port.Li2.restrictedPoleFunctional μ w (Port.Li2.integralPoleMulRegular c g f r)
    (Port.Li2.integralPoleMulResidue c g r)
private theorem poleMultiplierFunctional_add (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X])
    (g h f : PowerSeries (PadicInt ℓ))
    (hg : PowerSeries.IsRestricted 1 g) (hh : PowerSeries.IsRestricted 1 h)
    (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ) :
    poleMultiplierFunctional c μ w f r (g+h)=
      poleMultiplierFunctional c μ w f r g+poleMultiplierFunctional c μ w f r h := by
  unfold poleMultiplierFunctional
  obtain ⟨hreg,hres⟩:=pole_mul_add c hc g h f hg hh hf r
  rw [hreg,hres]
  exact Port.Li2.restrictedPoleFunctional_add μ w _ _
    (Port.Li2.integralPoleMulRegular_isRestricted c g f hg hf r)
    (Port.Li2.integralPoleMulRegular_isRestricted c h f hh hf r) _ _
private theorem poleMultiplierFunctional_smul (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (g f : PowerSeries (PadicInt ℓ))
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : ι→PadicInt ℓ) (a : PadicInt ℓ) :
    poleMultiplierFunctional c μ w f r (a • g)=C a*poleMultiplierFunctional c μ w f r g := by
  unfold poleMultiplierFunctional
  obtain ⟨hreg,hres⟩:=pole_mul_smul c hc g f hg hf r a
  rw [hreg,hres]
  exact Port.Li2.restrictedPoleFunctional_smul μ w _
    (Port.Li2.integralPoleMulRegular_isRestricted c g f hg hf r) _ a
private theorem poleMultiplierFunctional_bound (c : ι→PadicInt ℓ)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (g f : PowerSeries (PadicInt ℓ))
    (r : ι→PadicInt ℓ) (B : ℝ) (hB : 0≤B)
    (hg : ∀n,‖PowerSeries.coeff n g‖≤B) (n : ℕ) :
    ‖(poleMultiplierFunctional c μ w f r g).coeff n‖≤B := by
  apply Port.Li2.restrictedPoleFunctional_coeff_bound μ w _ _ B hB
  · exact Port.Li2.integralPoleMulRegular_bound_left c g f r B hB hg
  · exact Port.Li2.integralPoleMulResidue_bound_left c g r B hg
private theorem poleMultiplierFunctional_eval_bound (c : ι→PadicInt ℓ)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (g f : PowerSeries (PadicInt ℓ))
    (r : ι→PadicInt ℓ) (B : ℝ) (hB : 0≤B)
    (hg : ∀n,‖PowerSeries.coeff n g‖≤B) (y : PadicInt ℓ) :
    ‖(poleMultiplierFunctional c μ w f r g).eval y‖≤B := by
  rw [Polynomial.eval_eq_sum_range]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
  intro n hn
  rw [norm_mul,norm_pow]
  simpa only [mul_one] using mul_le_mul (poleMultiplierFunctional_bound c μ w g f r B hB hg n)
    (pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one y))
    (pow_nonneg (norm_nonneg y) n) hB
private theorem poleMultiplierFunctional_zero (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (f : PowerSeries (PadicInt ℓ))
    (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ) :
    poleMultiplierFunctional c μ w f r 0=0 := by
  have h:=poleMultiplierFunctional_smul c hc μ w f f hf hf r 0
  simpa only [zero_smul,map_zero,zero_mul] using h
private theorem poleMultiplierFunctional_neg (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (g f : PowerSeries (PadicInt ℓ))
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ) :
    poleMultiplierFunctional c μ w f r (-g)= -poleMultiplierFunctional c μ w f r g := by
  have h:=poleMultiplierFunctional_smul c hc μ w g f hg hf r (-1)
  simpa only [neg_one_smul,map_neg,map_one,neg_one_mul] using h
private theorem poleMultiplierFunctional_sub (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (g h f : PowerSeries (PadicInt ℓ))
    (hg : PowerSeries.IsRestricted 1 g) (hh : PowerSeries.IsRestricted 1 h)
    (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ) :
    poleMultiplierFunctional c μ w f r (g-h)=
      poleMultiplierFunctional c μ w f r g-poleMultiplierFunctional c μ w f r h := by
  rw [sub_eq_add_neg,poleMultiplierFunctional_add c hc μ w g (-h) f hg
    (PowerSeries.isRestricted.neg 1 hh) hf r,poleMultiplierFunctional_neg c hc μ w h f hh hf r]
  rfl
private theorem poleMultiplierFunctional_sum (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (f : PowerSeries (PadicInt ℓ))
    (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ)
    {κ : Type*} (S : Finset κ) (g : κ→PowerSeries (PadicInt ℓ))
    (hg : ∀i∈S,PowerSeries.IsRestricted 1 (g i)) :
    poleMultiplierFunctional c μ w f r (∑ i∈S,g i)=
      ∑ i∈S,poleMultiplierFunctional c μ w f r (g i) := by
  classical
  induction S using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty,poleMultiplierFunctional_zero c hc μ w f hf r]
  | @insert i S hi ih=>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,
      poleMultiplierFunctional_add c hc μ w (g i) (∑j∈S,g j) f
        (hg i (Finset.mem_insert_self _ _))
        (Port.Li2.restricted_finset_sum S g (fun j hj=>hg j (Finset.mem_insert_of_mem hj))) hf r,
      ih (fun j hj=>hg j (Finset.mem_insert_of_mem hj))]
private theorem poleMultiplierFunctional_trunc (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (g f : PowerSeries (PadicInt ℓ))
    (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ) (N : ℕ) :
    poleMultiplierFunctional c μ w f r (PowerSeries.trunc N g : PowerSeries (PadicInt ℓ))=
      ∑ j∈Finset.range N,C (PowerSeries.coeff j g)*
        poleMultiplierFunctional c μ w f r (PowerSeries.X^j) := by
  rw [PowerSeries.trunc_apply,Nat.Ico_zero_eq_range,Port.Li2.polynomial_coe_finset_sum,
    poleMultiplierFunctional_sum c hc μ w f hf r]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [←Polynomial.C_mul_X_pow_eq_monomial,Polynomial.coe_mul,Polynomial.coe_C,Polynomial.coe_pow,Polynomial.coe_X]
    have hsmul : (PowerSeries.coeff j g) • (PowerSeries.X^j:PowerSeries (PadicInt ℓ))=
        PowerSeries.C (PowerSeries.coeff j g)*PowerSeries.X^j:=by rw [Algebra.smul_def];rfl
    rw [←hsmul]
    exact poleMultiplierFunctional_smul c hc μ w _ f
      (by simpa only [←Polynomial.coe_X,←Polynomial.coe_pow] using Port.Li2.polynomial_isRestricted ((X:Polynomial (PadicInt ℓ))^j)) hf r _
  · intro j hj
    exact Port.Li2.polynomial_isRestricted _
private theorem poleMultiplierFunctional_trunc_tendsto (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (g f : PowerSeries (PadicInt ℓ))
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ)
    (ρ : ℝ) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (hbound : ∀j,‖PowerSeries.coeff j g‖≤ρ^j)
    (y : PadicInt ℓ) :
    Tendsto (fun N=> (poleMultiplierFunctional c μ w f r (PowerSeries.trunc N g : PowerSeries (PadicInt ℓ))).eval y)
      atTop (𝓝 ((poleMultiplierFunctional c μ w f r g).eval y)) := by
  rw [←tendsto_sub_nhds_zero_iff,tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun N=>norm_nonneg _) (fun N=>?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1)
  have hN : PowerSeries.IsRestricted 1 (PowerSeries.trunc N g : PowerSeries (PadicInt ℓ)):=
    Port.Li2.polynomial_isRestricted _
  have ht : ∀j,‖PowerSeries.coeff j (g-(PowerSeries.trunc N g : PowerSeries (PadicInt ℓ)))‖≤ρ^N:=by
    intro j
    simp only [map_sub,Polynomial.coeff_coe,PowerSeries.coeff_trunc]
    by_cases hj : j<N
    · simp only [if_pos hj,sub_self,norm_zero]
      exact pow_nonneg hρ0 N
    · simp only [if_neg hj,sub_zero]
      exact (hbound j).trans (pow_le_pow_of_le_one hρ0 hρ1.le (by omega))
  have he:=poleMultiplierFunctional_eval_bound c μ w (g-(PowerSeries.trunc N g : PowerSeries (PadicInt ℓ)))
    f r (ρ^N) (pow_nonneg hρ0 N) ht y
  rw [poleMultiplierFunctional_sub c hc μ w g _ f hg hN hf r,eval_sub,norm_sub_rev] at he
  exact he

private theorem poleMultiplierFunctional_series (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (g f : PowerSeries (PadicInt ℓ))
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ)
    (ρ : ℝ) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (hbound : ∀j,‖PowerSeries.coeff j g‖≤ρ^j)
    (y : PadicInt ℓ) :
    (poleMultiplierFunctional c μ w f r g).eval y=
      ∑' j,PowerSeries.coeff j g*(poleMultiplierFunctional c μ w f r (PowerSeries.X^j)).eval y := by
  let a : ℕ→PadicInt ℓ:=fun j=>PowerSeries.coeff j g*
    (poleMultiplierFunctional c μ w f r (PowerSeries.X^j)).eval y
  have hs : Summable a:=by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop,tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun j=>norm_nonneg _) (fun j=>?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1)
    dsimp only [a]
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans (hbound j)
  have ht:=poleMultiplierFunctional_trunc_tendsto c hc μ w g f hg hf r ρ hρ0 hρ1 hbound y
  have he (N : ℕ) : (poleMultiplierFunctional c μ w f r
      (PowerSeries.trunc N g : PowerSeries (PadicInt ℓ))).eval y=∑ j∈Finset.range N,a j:=by
    rw [poleMultiplierFunctional_trunc c hc μ w g f hf r N,eval_finset_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [a,eval_mul,eval_C]
  simp_rw [he] at ht
  exact tendsto_nhds_unique ht hs.hasSum.tendsto_sum_nat


private theorem classV_series (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hu : z^ℓ≠0∧padicValRat ℓ (z^ℓ)=0) (hreg : Port.Li2.VG ℓ (z^ℓ/(1-z^ℓ)) 0)
    (hw : z^ℓ≠1) (hR : Range n ℓ) (s : Fin ℓ) (ξ : Padic ℓ) (d : ℕ)
    (f : PowerSeries (PadicInt ℓ)) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin ℓ→PadicInt ℓ)
    (he : atZeroPadic ℓ (rfX^d*classWeight n ℓ s)*
      integralHahnHom ℓ (Port.Li2.integralPoleDenominator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)):PowerSeries (PadicInt ℓ))=
      integralHahnHom ℓ (Port.Li2.integralPoleNumerator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)) f r))
    (g : PowerSeries (PadicInt ℓ)) (hg : PowerSeries.IsRestricted 1 g)
    (ρ : ℝ) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (hbound : ∀j,‖PowerSeries.coeff j g‖≤ρ^j)
    (y : PadicInt ℓ) (hy : (y:Padic ℓ)=(ℓ:Padic ℓ)^2*ξ) :
    (Port.Unified.Proofs.Hermite.generalPoleV (z^ℓ) hu hreg
      (Port.Li2.integralPoleMulRegular Port.Unified.Proofs.Hermite.generalPoleCenters g f r)
      (Port.Li2.integralPoleMulResidue Port.Unified.Proofs.Hermite.generalPoleCenters g r)).eval₂
        (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)=
      ∑'j,((PowerSeries.coeff j g:PadicInt ℓ):Padic ℓ)*localV z ℓ ξ (rfX^(d+j)*classWeight n ℓ s) := by
  let c:=Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)
  let μ:=Port.Li2.derivativeMoments (Port.Li2.integralParameterMoment (z^ℓ) hreg)
  let w : Fin ℓ→(PadicInt ℓ)[X]:=fun m=>Port.Li2.integralVPole (z^ℓ) hu.1 hu.2 m.val m.isLt
  let T:=poleMultiplierFunctional c μ w f r
  have heval (P : (PadicInt ℓ)[X]) : P.eval₂ (algebraMap (PadicInt ℓ) (Padic ℓ)) (y:Padic ℓ)=
      ((P.eval y:PadicInt ℓ):Padic ℓ):=by
    simpa only [PadicInt.algebraMap_apply] using
      (Polynomial.eval₂_at_apply (p:=P) (algebraMap (PadicInt ℓ) (Padic ℓ)) y)
  have hmon (j : ℕ) : (((T (PowerSeries.X^j)).eval y:PadicInt ℓ):Padic ℓ)=
      localV z ℓ ξ (rfX^(d+j)*classWeight n ℓ s):=by
    have hh:=classV_monomial z n ℓ hu hreg hw hR s ξ d j f hf r he
    rw [←hy,heval] at hh
    exact hh
  have hs : Summable (fun j=>PowerSeries.coeff j g*(T (PowerSeries.X^j)).eval y):=by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop,tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun j=>norm_nonneg _) (fun j=>?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans (hbound j)
  have hsum:=poleMultiplierFunctional_series c
    Port.Unified.Proofs.Hermite.generalPoleCenters_injective μ w g f hg hf r ρ hρ0 hρ1 hbound y
  have hc:=congrArg (fun a : PadicInt ℓ=>(a:Padic ℓ)) hsum
  have hmap:=hs.map_tsum PadicInt.Coe.ringHom PadicInt.isOpenEmbedding_coe.continuous
  rw [←hy,heval]
  change (((T g).eval y:PadicInt ℓ):Padic ℓ)=_
  simp only [PadicInt.Coe.ringHom_apply] at hmap
  rw [hc,hmap]
  apply tsum_congr
  intro j
  simp only [PadicInt.Coe.ringHom_apply,PadicInt.coe_mul,hmon]

open Port.Li2
private theorem divDiff_X (c : PadicInt ℓ) :
    restrictedDivDiff c PowerSeries.X=1 := by
  apply PowerSeries.ext
  intro n
  simp only [restrictedDivDiff,PowerSeries.coeff_mk,PowerSeries.coeff_X,
    PowerSeries.coeff_one]
  by_cases hn : n=0
  · subst n
    simp
  · have he (k : ℕ) : n+k+1≠1:=by omega
    simp only [he,ite_false,zero_mul,tsum_zero]
    simp [hn]
private theorem pole_mul_X (c : ι→PadicInt ℓ) (f : PowerSeries (PadicInt ℓ))
    (r : ι→PadicInt ℓ) :
    integralPoleMulRegular c PowerSeries.X f r=PowerSeries.X*f+∑i,PowerSeries.C (r i) ∧
    integralPoleMulResidue c PowerSeries.X r=fun i=>r i*c i := by
  constructor
  · simp only [integralPoleMulRegular,divDiff_X,mul_one]
  · funext i
    unfold integralPoleMulResidue
    have he:=restrictedEval_polynomial (c i) (X:(PadicInt ℓ)[X])
    simpa only [Polynomial.coe_X,Polynomial.eval_X] using congrArg (fun a=>r i*a) he
private theorem restrictedV_X (μ : ℕ→PadicInt ℓ) (f : PowerSeries (PadicInt ℓ))
    (hf : PowerSeries.IsRestricted 1 f) :
    restrictedV μ (PowerSeries.X*f)=restrictedU μ f := by
  have hX : PowerSeries.IsRestricted 1 (PowerSeries.X:PowerSeries (PadicInt ℓ)):=by
    simpa only [Polynomial.coe_X] using polynomial_isRestricted (X:(PadicInt ℓ)[X])
  rw [restrictedV_derivative μ _ (PowerSeries.isRestricted.mul 1 hX hf),restrictedU_derivative]
private theorem restrictedV_constant (μ : ℕ→PadicInt ℓ) (a : PadicInt ℓ) :
    restrictedV μ (PowerSeries.C a)=0 := by
  have hC : PowerSeries.IsRestricted 1 (PowerSeries.C a):=by
    simpa only [Polynomial.coe_C] using polynomial_isRestricted (C a)
  rw [restrictedV_derivative μ _ hC]
  simp [restrictedMoment]

private theorem pole_functional_U_eq_VX (c : ι→PadicInt ℓ) (μ : ℕ→PadicInt ℓ)
    (w : ι→(PadicInt ℓ)[X]) (f : PowerSeries (PadicInt ℓ))
    (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ) :
    restrictedPoleFunctional (fun n=>((n+1:ℕ):PadicInt ℓ)*μ n) (fun i=>C (c i)*w i) f r=
      restrictedPoleFunctional (derivativeMoments μ) w
        (integralPoleMulRegular c PowerSeries.X f r)
        (integralPoleMulResidue c PowerSeries.X r) := by
  rw [(pole_mul_X c f r).1,(pole_mul_X c f r).2]
  have hreg : restrictedMoment (derivativeMoments μ)
      (PowerSeries.X*f+∑i,PowerSeries.C (r i))=restrictedU μ f := by
    rw [←map_sum]
    have hX : PowerSeries.IsRestricted 1 (PowerSeries.X:PowerSeries (PadicInt ℓ)):=by
      simpa only [Polynomial.coe_X] using polynomial_isRestricted (X:(PadicInt ℓ)[X])
    have hC : PowerSeries.IsRestricted 1 (PowerSeries.C (∑i,r i)):=by
      simpa only [Polynomial.coe_C] using polynomial_isRestricted (C (∑i,r i))
    change restrictedV μ _=_
    rw [restrictedV_derivative μ _ (PowerSeries.isRestricted.add 1
      (PowerSeries.isRestricted.mul 1 hX hf) hC),map_add,PowerSeries.derivative_C,add_zero,
      ←restrictedU_derivative]
  unfold restrictedPoleFunctional
  rw [hreg]
  change C (restrictedU μ f)+_=C (restrictedU μ f)+_
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_mul]
  ring

private theorem generalPoleU_eq_VX (z : ℚ) (hunit : z≠0∧padicValRat ℓ z=0)
    (hreg : Port.Li2.VG ℓ (z/(1-z)) 0)
    (f : PowerSeries (PadicInt ℓ)) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin ℓ→PadicInt ℓ) :
    Port.Unified.Proofs.Hermite.generalPoleU z hunit hreg f r=
      Port.Unified.Proofs.Hermite.generalPoleV z hunit hreg
        (integralPoleMulRegular Port.Unified.Proofs.Hermite.generalPoleCenters PowerSeries.X f r)
        (integralPoleMulResidue Port.Unified.Proofs.Hermite.generalPoleCenters PowerSeries.X r) := by
  unfold Port.Unified.Proofs.Hermite.generalPoleU Port.Unified.Proofs.Hermite.generalPoleV
  rw [←pole_functional_U_eq_VX _ _ _ _ hf]
  congr 1
  funext i
  simp only [Port.Unified.Proofs.Hermite.generalPoleCenters,integralUPole,integralVPole,
    map_neg,map_mul]
  ring
private theorem pole_mul_mul (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (a b f : PowerSeries (PadicInt ℓ))
    (ha : PowerSeries.IsRestricted 1 a) (hb : PowerSeries.IsRestricted 1 b)
    (hf : PowerSeries.IsRestricted 1 f) (r : ι→PadicInt ℓ) :
    Port.Li2.integralPoleMulRegular c a
      (Port.Li2.integralPoleMulRegular c b f r) (Port.Li2.integralPoleMulResidue c b r)=
      Port.Li2.integralPoleMulRegular c (a*b) f r ∧
    Port.Li2.integralPoleMulResidue c a (Port.Li2.integralPoleMulResidue c b r)=
      Port.Li2.integralPoleMulResidue c (a*b) r := by
  apply Port.Li2.integralPoleNumerator_injective c hc _ _
    (Port.Li2.integralPoleMulRegular_isRestricted c a _ ha
      (Port.Li2.integralPoleMulRegular_isRestricted c b f hb hf r) _)
    (Port.Li2.integralPoleMulRegular_isRestricted c (a*b) f (PowerSeries.isRestricted.mul 1 ha hb) hf r)
  rw [Port.Li2.integralPoleNumerator_mul c a _ ha,
    Port.Li2.integralPoleNumerator_mul c b f hb,
    Port.Li2.integralPoleNumerator_mul c (a*b) f (PowerSeries.isRestricted.mul 1 ha hb)]
  ring
private theorem generalU_multiplier (z : ℚ) (hunit : z≠0∧padicValRat ℓ z=0)
    (hreg : Port.Li2.VG ℓ (z/(1-z)) 0)
    (g f : PowerSeries (PadicInt ℓ)) (hg : PowerSeries.IsRestricted 1 g)
    (hf : PowerSeries.IsRestricted 1 f) (r : Fin ℓ→PadicInt ℓ) :
    Port.Unified.Proofs.Hermite.generalPoleU z hunit hreg
      (integralPoleMulRegular Port.Unified.Proofs.Hermite.generalPoleCenters g f r)
      (integralPoleMulResidue Port.Unified.Proofs.Hermite.generalPoleCenters g r)=
      poleMultiplierFunctional Port.Unified.Proofs.Hermite.generalPoleCenters
        (derivativeMoments (integralParameterMoment z hreg))
        (fun m : Fin ℓ=>integralVPole z hunit.1 hunit.2 m.val m.isLt) f r (PowerSeries.X*g) := by
  rw [generalPoleU_eq_VX z hunit hreg _
    (integralPoleMulRegular_isRestricted _ _ _ hg hf _) _]
  have hX : PowerSeries.IsRestricted 1 (PowerSeries.X:PowerSeries (PadicInt ℓ)):=by
    simpa only [Polynomial.coe_X] using polynomial_isRestricted (X:(PadicInt ℓ)[X])
  have he:=pole_mul_mul Port.Unified.Proofs.Hermite.generalPoleCenters
    Port.Unified.Proofs.Hermite.generalPoleCenters_injective PowerSeries.X g f hX hg hf r
  rw [he.1,he.2]
  rfl
private def germScaled (ℓ : ℕ) [Fact ℓ.Prime] (Ψ : Germ ℓ) : PowerSeries (PadicInt ℓ):=
  PowerSeries.mk (fun j=>Ψ j*(ℓ:PadicInt ℓ)^j)
private def chiScaled (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (Ψ : Germ ℓ) : PowerSeries (PadicInt ℓ):=
  germScaled ℓ (chi ℓ s Ψ)
private theorem chiScaled_zero (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (Ψ : Germ ℓ) (hs : s.val=0) :
    chiScaled ℓ s Ψ=germScaled ℓ Ψ := by
  apply PowerSeries.ext
  intro j
  simp only [chiScaled,germScaled,PowerSeries.coeff_mk,chi,hs,ite_true]
private theorem chiScaled_nonzero (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (Ψ : Germ ℓ) (hs : s.val≠0) :
    chiScaled ℓ s Ψ=(PowerSeries.C (ℓ:PadicInt ℓ)*PowerSeries.X-PowerSeries.C (s.val:PadicInt ℓ))*germScaled ℓ Ψ := by
  rw [show (PowerSeries.C (ℓ:PadicInt ℓ)*PowerSeries.X-PowerSeries.C (s.val:PadicInt ℓ))*germScaled ℓ Ψ=
    PowerSeries.C (ℓ:PadicInt ℓ)*(PowerSeries.X*germScaled ℓ Ψ)-PowerSeries.C (s.val:PadicInt ℓ)*germScaled ℓ Ψ by ring]
  apply PowerSeries.ext
  intro j
  simp only [chiScaled,germScaled,PowerSeries.coeff_mk,map_sub,PowerSeries.coeff_C_mul]
  cases j with
  | zero=>simp [chi,hs]
  | succ j=>
    rw [PowerSeries.coeff_succ_X_mul]
    simp only [germScaled,PowerSeries.coeff_mk,chi,if_neg hs,Nat.succ_ne_zero,ite_false,
      Nat.succ_sub_one,pow_succ]
    ring
private theorem germScaled_bound (ℓ : ℕ) [Fact ℓ.Prime] (Ψ : Germ ℓ) (j : ℕ) :
    ‖PowerSeries.coeff j (germScaled ℓ Ψ)‖≤‖(ℓ:PadicInt ℓ)‖^j := by
  simp only [germScaled,PowerSeries.coeff_mk,norm_mul,norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) j) (PadicInt.norm_le_one _)
private theorem germScaled_restricted (ℓ : ℕ) [Fact ℓ.Prime] (Ψ : Germ ℓ) :
    PowerSeries.IsRestricted 1 (germScaled ℓ Ψ) := by
  rw [PowerSeries.isRestricted_iff']
  simp only [one_pow,mul_one]
  exact squeeze_zero (fun j=>norm_nonneg _) (germScaled_bound ℓ Ψ)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) Port.Li2.padicInt_prime_norm_lt_one)

private theorem poleMultiplierFunctional_C_mul (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X]) (g f : PowerSeries (PadicInt ℓ))
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : ι→PadicInt ℓ) (a : PadicInt ℓ) :
    poleMultiplierFunctional c μ w f r (PowerSeries.C a*g)=
      C a*poleMultiplierFunctional c μ w f r g := by
  have he : a • g=PowerSeries.C a*g:=by rw [Algebra.smul_def];rfl
  rw [←he,poleMultiplierFunctional_smul c hc μ w g f hg hf r a]
private theorem chi_functional_nonzero (c : ι→PadicInt ℓ) (hc : Function.Injective c)
    (μ : ℕ→PadicInt ℓ) (w : ι→(PadicInt ℓ)[X])
    (f : PowerSeries (PadicInt ℓ)) (hf : PowerSeries.IsRestricted 1 f)
    (r : ι→PadicInt ℓ) (s : Fin ℓ) (Ψ : Germ ℓ) (hs : s.val≠0) :
    poleMultiplierFunctional c μ w f r (chiScaled ℓ s Ψ)=
      C (ℓ:PadicInt ℓ)*poleMultiplierFunctional c μ w f r (PowerSeries.X*germScaled ℓ Ψ)-
      C (s.val:PadicInt ℓ)*poleMultiplierFunctional c μ w f r (germScaled ℓ Ψ) := by
  rw [chiScaled_nonzero ℓ s Ψ hs]
  rw [show (PowerSeries.C (ℓ:PadicInt ℓ)*PowerSeries.X-PowerSeries.C (s.val:PadicInt ℓ))*germScaled ℓ Ψ=
    PowerSeries.C (ℓ:PadicInt ℓ)*(PowerSeries.X*germScaled ℓ Ψ)-PowerSeries.C (s.val:PadicInt ℓ)*germScaled ℓ Ψ by ring]
  have hX : PowerSeries.IsRestricted 1 (PowerSeries.X:PowerSeries (PadicInt ℓ)):=by
    simpa only [Polynomial.coe_X] using polynomial_isRestricted (X:(PadicInt ℓ)[X])
  have hL : PowerSeries.IsRestricted 1 (PowerSeries.C (ℓ:PadicInt ℓ)):=by
    simpa only [Polynomial.coe_C] using polynomial_isRestricted (C (ℓ:PadicInt ℓ))
  have hS : PowerSeries.IsRestricted 1 (PowerSeries.C (s.val:PadicInt ℓ)):=by
    simpa only [Polynomial.coe_C] using polynomial_isRestricted (C (s.val:PadicInt ℓ))
  rw [poleMultiplierFunctional_sub c hc μ w _ _ f
    (PowerSeries.isRestricted.mul 1 hL (PowerSeries.isRestricted.mul 1 hX (germScaled_restricted ℓ Ψ)))
    (PowerSeries.isRestricted.mul 1 hS (germScaled_restricted ℓ Ψ)) hf r,
    poleMultiplierFunctional_C_mul c hc μ w _ f
      (PowerSeries.isRestricted.mul 1 hX (germScaled_restricted ℓ Ψ)) hf r,
    poleMultiplierFunctional_C_mul c hc μ w _ f (germScaled_restricted ℓ Ψ) hf r]

private theorem generalUV_chi_nonzero (z : ℚ) (hunit : z≠0∧padicValRat ℓ z=0)
    (hreg : Port.Li2.VG ℓ (z/(1-z)) 0)
    (f : PowerSeries (PadicInt ℓ)) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin ℓ→PadicInt ℓ) (s : Fin ℓ) (Ψ : Germ ℓ) (hs : s.val≠0) (Y : Padic ℓ) :
    (Port.Unified.Proofs.Hermite.generalPoleU z hunit hreg
      (integralPoleMulRegular Port.Unified.Proofs.Hermite.generalPoleCenters (germScaled ℓ Ψ) f r)
      (integralPoleMulResidue Port.Unified.Proofs.Hermite.generalPoleCenters (germScaled ℓ Ψ) r)).eval₂
        (algebraMap (PadicInt ℓ) (Padic ℓ)) Y-
      (s.val:Padic ℓ)/(ℓ:Padic ℓ)*
      (Port.Unified.Proofs.Hermite.generalPoleV z hunit hreg
        (integralPoleMulRegular Port.Unified.Proofs.Hermite.generalPoleCenters (germScaled ℓ Ψ) f r)
        (integralPoleMulResidue Port.Unified.Proofs.Hermite.generalPoleCenters (germScaled ℓ Ψ) r)).eval₂
          (algebraMap (PadicInt ℓ) (Padic ℓ)) Y=
      (ℓ:Padic ℓ)⁻¹*
        (Port.Unified.Proofs.Hermite.generalPoleV z hunit hreg
          (integralPoleMulRegular Port.Unified.Proofs.Hermite.generalPoleCenters (chiScaled ℓ s Ψ) f r)
          (integralPoleMulResidue Port.Unified.Proofs.Hermite.generalPoleCenters (chiScaled ℓ s Ψ) r)).eval₂
            (algebraMap (PadicInt ℓ) (Padic ℓ)) Y := by
  let c:=Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)
  let μ:=derivativeMoments (integralParameterMoment z hreg)
  let w : Fin ℓ→(PadicInt ℓ)[X]:=fun m=>integralVPole z hunit.1 hunit.2 m.val m.isLt
  have ht:=chi_functional_nonzero c Port.Unified.Proofs.Hermite.generalPoleCenters_injective
    μ w f hf r s Ψ hs
  have hval:=congrArg (fun P : (PadicInt ℓ)[X]=>P.eval₂ (algebraMap (PadicInt ℓ) (Padic ℓ)) Y) ht
  simp only [eval₂_sub,eval₂_mul,eval₂_C,PadicInt.algebraMap_apply,PadicInt.coe_natCast] at hval
  rw [generalU_multiplier z hunit hreg _ f (germScaled_restricted ℓ Ψ) hf r]
  change (poleMultiplierFunctional c μ w f r (PowerSeries.X*germScaled ℓ Ψ)).eval₂ _ Y-
    (s.val:Padic ℓ)/(ℓ:Padic ℓ)*(poleMultiplierFunctional c μ w f r (germScaled ℓ Ψ)).eval₂ _ Y=
      (ℓ:Padic ℓ)⁻¹*(poleMultiplierFunctional c μ w f r (chiScaled ℓ s Ψ)).eval₂ _ Y
  rw [hval]
  have hp : (ℓ:Padic ℓ)≠0:=by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  field_simp [hp]
  <;> ring

private theorem class_nonzero_series (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hu : z^ℓ≠0∧padicValRat ℓ (z^ℓ)=0) (hreg : Port.Li2.VG ℓ (z^ℓ/(1-z^ℓ)) 0)
    (hw : z^ℓ≠1) (hR : Range n ℓ) (s : Fin ℓ) (hs : s.val≠0)
    (ξ : Padic ℓ) (d : ℕ) (Ψ : Germ ℓ)
    (f : PowerSeries (PadicInt ℓ)) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin ℓ→PadicInt ℓ)
    (he : atZeroPadic ℓ (rfX^d*classWeight n ℓ s)*
      integralHahnHom ℓ (Port.Li2.integralPoleDenominator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)):PowerSeries (PadicInt ℓ))=
      integralHahnHom ℓ (Port.Li2.integralPoleNumerator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)) f r))
    (y : PadicInt ℓ) (hy : (y:Padic ℓ)=(ℓ:Padic ℓ)^2*ξ) :
    (Port.Unified.Proofs.Hermite.generalPoleU (z^ℓ) hu hreg
      (integralPoleMulRegular Port.Unified.Proofs.Hermite.generalPoleCenters (germScaled ℓ Ψ) f r)
      (integralPoleMulResidue Port.Unified.Proofs.Hermite.generalPoleCenters (germScaled ℓ Ψ) r)).eval₂
        (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)-
      (s.val:Padic ℓ)/(ℓ:Padic ℓ)*
      (Port.Unified.Proofs.Hermite.generalPoleV (z^ℓ) hu hreg
        (integralPoleMulRegular Port.Unified.Proofs.Hermite.generalPoleCenters (germScaled ℓ Ψ) f r)
        (integralPoleMulResidue Port.Unified.Proofs.Hermite.generalPoleCenters (germScaled ℓ Ψ) r)).eval₂
          (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)=
      (ℓ:Padic ℓ)⁻¹*∑'j,(ℓ:Padic ℓ)^j*(chi ℓ s Ψ j:Padic ℓ)*
        localV z ℓ ξ (rfX^(d+j)*classWeight n ℓ s) := by
  rw [generalUV_chi_nonzero (z^ℓ) hu hreg f hf r s Ψ hs]
  rw [classV_series z n ℓ hu hreg hw hR s ξ d f hf r he
    (chiScaled ℓ s Ψ) (germScaled_restricted ℓ (chi ℓ s Ψ))
    ‖(ℓ:PadicInt ℓ)‖ (norm_nonneg _) Port.Li2.padicInt_prime_norm_lt_one
    (germScaled_bound ℓ (chi ℓ s Ψ)) y hy]
  congr 1
  apply tsum_congr
  intro j
  simp only [chiScaled,germScaled,PowerSeries.coeff_mk,PadicInt.coe_mul,
    PadicInt.coe_pow,PadicInt.coe_natCast]
  ring

private theorem class_zero_series (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hu : z^ℓ≠0∧padicValRat ℓ (z^ℓ)=0) (hreg : Port.Li2.VG ℓ (z^ℓ/(1-z^ℓ)) 0)
    (hw : z^ℓ≠1) (hR : Range n ℓ) (s : Fin ℓ)
    (ξ : Padic ℓ) (d : ℕ) (Ψ : Germ ℓ)
    (f : PowerSeries (PadicInt ℓ)) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin ℓ→PadicInt ℓ)
    (he : atZeroPadic ℓ (rfX^d*classWeight n ℓ s)*
      integralHahnHom ℓ (Port.Li2.integralPoleDenominator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)):PowerSeries (PadicInt ℓ))=
      integralHahnHom ℓ (Port.Li2.integralPoleNumerator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)) f r))
    (y : PadicInt ℓ) (hy : (y:Padic ℓ)=(ℓ:Padic ℓ)^2*ξ) :
    (Port.Unified.Proofs.Hermite.generalPoleU (z^ℓ) hu hreg
      (integralPoleMulRegular Port.Unified.Proofs.Hermite.generalPoleCenters (germScaled ℓ Ψ) f r)
      (integralPoleMulResidue Port.Unified.Proofs.Hermite.generalPoleCenters (germScaled ℓ Ψ) r)).eval₂
        (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)=
      ∑'j,(ℓ:Padic ℓ)^j*(Ψ j:Padic ℓ)*
        localV z ℓ ξ (rfX^(d+1+j)*classWeight n ℓ s) := by
  let c:=Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)
  let fX:=integralPoleMulRegular c PowerSeries.X f r
  let rX:=integralPoleMulResidue c PowerSeries.X r
  have hX : PowerSeries.IsRestricted 1 (PowerSeries.X:PowerSeries (PadicInt ℓ)):=by
    simpa only [Polynomial.coe_X] using polynomial_isRestricted (X:(PadicInt ℓ)[X])
  have hfX : PowerSeries.IsRestricted 1 fX:=integralPoleMulRegular_isRestricted c _ f hX hf r
  have heX : atZeroPadic ℓ (rfX^(d+1)*classWeight n ℓ s)*
      integralHahnHom ℓ (integralPoleDenominator c:PowerSeries (PadicInt ℓ))=
      integralHahnHom ℓ (integralPoleNumerator c fX rX):=by
    rw [integralPoleNumerator_mul c _ f hX,map_mul,←he]
    rw [show (rfX:RatFunc ℚ)^(d+1)*classWeight n ℓ s=
      rfX*(rfX^d*classWeight n ℓ s) by rw [pow_succ];ring,atZeroPadic_mul,atZero_rfX]
    ring
  have ht:=classV_series z n ℓ hu hreg hw hR s ξ (d+1) fX hfX rX heX
    (germScaled ℓ Ψ) (germScaled_restricted ℓ Ψ)
    ‖(ℓ:PadicInt ℓ)‖ (norm_nonneg _) Port.Li2.padicInt_prime_norm_lt_one
    (germScaled_bound ℓ Ψ) y hy
  have hm:=pole_mul_mul c Port.Unified.Proofs.Hermite.generalPoleCenters_injective
    (germScaled ℓ Ψ) PowerSeries.X f (germScaled_restricted ℓ Ψ) hX hf r
  change (Port.Unified.Proofs.Hermite.generalPoleV (z^ℓ) hu hreg
    (integralPoleMulRegular c (germScaled ℓ Ψ) (integralPoleMulRegular c PowerSeries.X f r)
      (integralPoleMulResidue c PowerSeries.X r))
    (integralPoleMulResidue c (germScaled ℓ Ψ) (integralPoleMulResidue c PowerSeries.X r))).eval₂ _ _=_ at ht
  rw [hm.1,hm.2,mul_comm (germScaled ℓ Ψ) PowerSeries.X] at ht
  rw [generalU_multiplier (z^ℓ) hu hreg _ f (germScaled_restricted ℓ Ψ) hf r]
  change (Port.Unified.Proofs.Hermite.generalPoleV (z^ℓ) hu hreg
    (integralPoleMulRegular c (PowerSeries.X*germScaled ℓ Ψ) f r)
    (integralPoleMulResidue c (PowerSeries.X*germScaled ℓ Ψ) r)).eval₂ _ _=_
  rw [ht]
  apply tsum_congr
  intro j
  simp only [germScaled,PowerSeries.coeff_mk,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_natCast]
  ring

private def germHom (ℓ : ℕ) [Fact ℓ.Prime] :
    PowerSeries (PadicInt ℓ)→+*HahnSeries ℤ (Padic ℓ):=
  (HahnSeries.ofPowerSeries ℤ (Padic ℓ)).comp
    ((PowerSeries.rescale (ℓ:Padic ℓ)).comp (PowerSeries.map PadicInt.Coe.ringHom))

private theorem germHom_mk (ℓ : ℕ) [Fact ℓ.Prime] (H : Germ ℓ) :
    germHom ℓ (PowerSeries.mk H)=germSeries ℓ H := by
  rw [germSeries_rescale]
  rfl

private theorem germHom_C (ℓ : ℕ) [Fact ℓ.Prime] (a : PadicInt ℓ) :
    germHom ℓ (PowerSeries.C a)=HahnSeries.C (a:Padic ℓ) := by
  unfold germHom
  simp only [RingHom.comp_apply,PowerSeries.map_C]
  have hc : PowerSeries.rescale (ℓ:Padic ℓ) (PowerSeries.C (a:Padic ℓ))=
      PowerSeries.C (a:Padic ℓ):=by
    apply PowerSeries.ext
    intro n
    by_cases hn : n=0 <;> simp [PowerSeries.coeff_rescale,PowerSeries.coeff_C,hn]
  change HahnSeries.ofPowerSeries ℤ (Padic ℓ)
    (PowerSeries.rescale (ℓ:Padic ℓ) (PowerSeries.C (a:Padic ℓ)))=_
  rw [hc,HahnSeries.ofPowerSeries_C]

private theorem regular_germ (ℓ : ℕ) [Fact ℓ.Prime]
    (A B C : PowerSeries (PadicInt ℓ))
    (hB : IsUnit (PowerSeries.constantCoeff B)) (hC : IsUnit (PowerSeries.constantCoeff C))
    (k : (PadicInt ℓ)ˣ)
    (hk : (k:PadicInt ℓ)*PowerSeries.constantCoeff B=(PowerSeries.constantCoeff A)^3) :
    ∃ Ψ : Germ ℓ,IsUnit (Ψ 0) ∧ Ψ 0=PowerSeries.constantCoeff C ∧
      HahnSeries.C ((k:PadicInt ℓ):Padic ℓ)*germSeries ℓ Ψ*germHom ℓ B=
        (germHom ℓ A)^3*germHom ℓ C := by
  let b : (PowerSeries (PadicInt ℓ))ˣ:=(PowerSeries.isUnit_iff_constantCoeff.mpr hB).unit
  have hb : (b:PowerSeries (PadicInt ℓ))=B:=IsUnit.unit_spec _
  let D : PowerSeries (PadicInt ℓ):=
    PowerSeries.C ((k⁻¹:(PadicInt ℓ)ˣ):PadicInt ℓ)*A^3*
      ((b⁻¹:(PowerSeries (PadicInt ℓ))ˣ):PowerSeries (PadicInt ℓ))*C
  have hD : D*B*PowerSeries.C (k:PadicInt ℓ)=A^3*C := by
    dsimp only [D]
    calc
      _=(PowerSeries.C (((k⁻¹:(PadicInt ℓ)ˣ):PadicInt ℓ)*(k:PadicInt ℓ)))*
          (((b⁻¹:(PowerSeries (PadicInt ℓ))ˣ):PowerSeries (PadicInt ℓ))*B)*(A^3*C) := by
        rw [map_mul]
        ring
      _=_:=by rw [←hb];simp
  have h0 : PowerSeries.constantCoeff D=PowerSeries.constantCoeff C := by
    have hh:=congrArg (PowerSeries.constantCoeff (R:=PadicInt ℓ)) hD
    simp only [map_mul,map_pow,PowerSeries.constantCoeff_C] at hh
    rw [←hk] at hh
    have hi : IsUnit ((k:PadicInt ℓ)*PowerSeries.constantCoeff B):=k.isUnit.mul hB
    exact (hi.mul_right_cancel (by linear_combination hh))
  let Ψ : Germ ℓ:=fun j=>PowerSeries.coeff j D
  have hΨ : Ψ 0=PowerSeries.constantCoeff C:=by
    simpa only [Ψ,PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
  refine ⟨Ψ,hΨ ▸ hC,hΨ,?_⟩
  have he : PowerSeries.mk Ψ=D:=by ext n;simp [Ψ]
  have hm:=congrArg (germHom ℓ) hD
  rw [(germHom ℓ).map_mul (D*B) (PowerSeries.C (k:PadicInt ℓ)),
    (germHom ℓ).map_mul D B,germHom_C,(germHom ℓ).map_mul (A^3) C,
    (germHom ℓ).map_pow A 3] at hm
  rw [←he,germHom_mk] at hm
  linear_combination hm


private theorem germHom_X (ℓ : ℕ) [Fact ℓ.Prime] :
    germHom ℓ PowerSeries.X=HahnSeries.C (ℓ:Padic ℓ)*hX := by
  change HahnSeries.ofPowerSeries ℤ (Padic ℓ)
    (PowerSeries.rescale (ℓ:Padic ℓ) (PowerSeries.map PadicInt.Coe.ringHom PowerSeries.X))=_
  rw [PowerSeries.map_X,PowerSeries.rescale_X,map_mul,HahnSeries.ofPowerSeries_C,HahnSeries.ofPowerSeries_X]
  rfl

private theorem germHom_integer_polynomial (ℓ : ℕ) [Fact ℓ.Prime] (P : ℤ[X]) :
    germHom ℓ ((P.map (Int.castRingHom (PadicInt ℓ))):PowerSeries (PadicInt ℓ))=
      affineRFHahn ℓ 0 (ℓ:ℚ) (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
        (rfPoly (P.map (Int.castRingHom ℚ))) := by
  let f : ℤ[X]→+*HahnSeries ℤ (Padic ℓ):=
    ((germHom ℓ).comp Polynomial.coeToPowerSeries.ringHom).comp
      (Polynomial.mapRingHom (Int.castRingHom (PadicInt ℓ)))
  let g : ℤ[X]→+*HahnSeries ℤ (Padic ℓ):=
    ((affineRFHahn ℓ 0 (ℓ:ℚ) (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)).comp
      (algebraMap ℚ[X] (RatFunc ℚ))).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))
  have he : f=g:=by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · dsimp only [f,g]
      simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,Polynomial.map_X,
        Polynomial.coeToPowerSeries.ringHom_apply,Polynomial.coe_X]
      change germHom ℓ (PowerSeries.X)=
        affineRFHahn ℓ 0 (ℓ:ℚ) (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero) (rfPoly X)
      rw [germHom_X,affineRFHahn_poly]
      simp only [X_comp,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
        map_add,map_mul,polyHahn_C,polyHahn_X,Int.cast_natCast,Rat.cast_natCast,Rat.cast_zero,
        map_zero,add_zero,eq_ratCast,map_natCast,Polynomial.map_natCast]
  exact DFunLike.congr_fun he P

private theorem germHom_integer_shift (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P : ℤ[X]) :
    germHom ℓ (((P.comp (X-C (s.val:ℤ))).map (Int.castRingHom (PadicInt ℓ))):PowerSeries (PadicInt ℓ))=
      atLocal (rfPoly (P.map (Int.castRingHom ℚ))) ℓ s := by
  rw [germHom_integer_polynomial,atLocal_eq_hom,affineRFHahn_poly,affineRFHahn_poly]
  congr 1
  simp only [Polynomial.map_comp,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    Int.coe_castRingHom,Int.cast_natCast,comp_assoc,X_comp,C_comp,sub_comp]
  congr 1
  simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,map_mul,map_add,map_zero,map_neg]
  ring_nf
  rw [Polynomial.map_sub,Polynomial.map_C]


private def nonmatchingInt (N ℓ : ℕ) (s : Fin ℓ) : ℤ[X]:=
  ∏ i∈(Finset.Icc 1 N).filter (fun i=>i%ℓ≠s.val),(X+C (i:ℤ))

private theorem nonmatchingInt_map (N ℓ : ℕ) (s : Fin ℓ) :
    (nonmatchingInt N ℓ s).map (Int.castRingHom ℚ)=
      ∏ i∈(Finset.Icc 1 N).filter (fun i=>i%ℓ≠s.val),(X+C (i:ℚ)) := by
  simp only [nonmatchingInt,Polynomial.map_prod,Polynomial.map_add,Polynomial.map_X,
    Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast]

private theorem nonmatching_constant_unit (N ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) :
    Unit ℓ (((nonmatchingInt N ℓ s).eval (-(s.val:ℤ)):ℤ):Padic ℓ) := by
  unfold Unit nonmatchingInt
  simp only [eval_prod,Int.cast_prod,norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  have hu:=nonmatching_unit ℓ s i (Finset.mem_filter.mp hi).2
  simpa only [Unit,eval_add,eval_X,eval_C,Int.cast_add,Int.cast_neg,Int.cast_natCast,
    Rat.cast_sub,Rat.cast_natCast,sub_eq_add_neg,add_comm] using! hu

private theorem kappaQ_constants (n ℓ : ℕ) (s : Fin ℓ) :
    kappaQ n ℓ s=(((nonmatchingInt n ℓ s).eval (-(s.val:ℤ)):ℤ):ℚ)^3/
      (((nonmatchingInt (4*n) ℓ s).eval (-(s.val:ℤ)):ℤ):ℚ) := by
  simp only [kappaQ,nonmatchingInt,eval_prod,eval_add,eval_X,eval_C,Int.cast_prod,
    Int.cast_add,Int.cast_neg,Int.cast_natCast,Finset.prod_pow,sub_eq_add_neg,add_comm]

private def shiftedIntegralSeries (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P : ℤ[X]) :
    PowerSeries (PadicInt ℓ):=
  ((P.comp (X-C (s.val:ℤ))).map (Int.castRingHom (PadicInt ℓ)):PowerSeries (PadicInt ℓ))

private theorem shiftedIntegralSeries_constant (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P : ℤ[X]) :
    PowerSeries.constantCoeff (shiftedIntegralSeries ℓ s P)=((P.eval (-(s.val:ℤ)):ℤ):PadicInt ℓ) := by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [shiftedIntegralSeries,Polynomial.coeff_coe,Polynomial.coeff_map,Int.coe_castRingHom]
  rw [Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_comp]
  simp only [eval_sub,eval_X,eval_C,zero_sub]

private theorem nonsingular_germ (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P Q : Ix n ℓ) :
    ∃ Ψ : Germ ℓ,IsUnit (Ψ 0) ∧
      (Ψ 0:Padic ℓ)=(((crtTailInt n ℓ s P*crtTailInt n ℓ s Q).eval (-(s.val:ℤ)):ℤ):Padic ℓ) ∧
      HahnSeries.C (kappa n ℓ s)*germSeries ℓ Ψ*
        atLocal (rfPoly ((nonmatchingInt (4*n) ℓ s).map (Int.castRingHom ℚ))) ℓ s=
      atLocal (rfPoly ((nonmatchingInt n ℓ s).map (Int.castRingHom ℚ))) ℓ s^3*
        atLocal (rfPoly ((crtTailInt n ℓ s P*crtTailInt n ℓ s Q).map (Int.castRingHom ℚ))) ℓ s := by
  let A:=shiftedIntegralSeries ℓ s (nonmatchingInt n ℓ s)
  let B:=shiftedIntegralSeries ℓ s (nonmatchingInt (4*n) ℓ s)
  let C:=shiftedIntegralSeries ℓ s (crtTailInt n ℓ s P*crtTailInt n ℓ s Q)
  have hB : IsUnit (PowerSeries.constantCoeff B):=by
    rw [show B=shiftedIntegralSeries ℓ s (nonmatchingInt (4*n) ℓ s) from rfl,
      shiftedIntegralSeries_constant,PadicInt.isUnit_iff]
    simpa only [Unit,PadicInt.norm_def,PadicInt.coe_intCast] using
      nonmatching_constant_unit (4*n) ℓ s
  have hC : IsUnit (PowerSeries.constantCoeff C):=by
    rw [show C=shiftedIntegralSeries ℓ s (crtTailInt n ℓ s P*crtTailInt n ℓ s Q) from rfl,
      shiftedIntegralSeries_constant,PadicInt.isUnit_iff]
    have hp:=crtTailInt_unit n ℓ s P
    have hq:=crtTailInt_unit n ℓ s Q
    simpa only [Unit,eval_mul,Int.cast_mul,norm_mul,PadicInt.norm_def,PadicInt.coe_intCast,
      one_mul] using! congrArg₂ (fun a b : ℝ=>a*b) hp hq
  let k0 : PadicInt ℓ:=⟨kappa n ℓ s,(kappa_unit n ℓ s).le⟩
  have hku : IsUnit k0:=PadicInt.isUnit_iff.mpr (kappa_unit n ℓ s)
  let ku : (PadicInt ℓ)ˣ:=hku.unit
  have hcoe : ((ku:PadicInt ℓ):Padic ℓ)=kappa n ℓ s:=by
    rw [show (ku:PadicInt ℓ)=k0 from IsUnit.unit_spec hku]
  have hk : (ku:PadicInt ℓ)*PowerSeries.constantCoeff B=(PowerSeries.constantCoeff A)^3:=by
    change (ku:PadicInt ℓ)*PowerSeries.constantCoeff (shiftedIntegralSeries ℓ s (nonmatchingInt (4*n) ℓ s))=
      (PowerSeries.constantCoeff (shiftedIntegralSeries ℓ s (nonmatchingInt n ℓ s)))^3
    rw [shiftedIntegralSeries_constant,shiftedIntegralSeries_constant]
    apply PadicInt.ext
    simp only [PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_intCast,hcoe]
    have hd : ((((nonmatchingInt (4*n) ℓ s).eval (-(s.val:ℤ)):ℤ):Padic ℓ))≠0:=by
      intro he
      have hh:=nonmatching_constant_unit (4*n) ℓ s
      simp only [Unit,he,norm_zero] at hh
      exact zero_ne_one hh
    rw [kappa,kappaQ_constants]
    push_cast
    exact div_mul_cancel₀ _ hd
  obtain ⟨Ψ,hunit,hzero,heq⟩:=regular_germ ℓ A B C hB hC ku hk
  refine ⟨Ψ,hunit,?_,?_⟩
  · have hh:=congrArg (fun x : PadicInt ℓ=>(x:Padic ℓ)) hzero
    simpa only [C,shiftedIntegralSeries_constant,PadicInt.coe_intCast] using! hh
  · dsimp only [A,B,C,shiftedIntegralSeries] at heq
    rw [germHom_integer_shift,germHom_integer_shift,germHom_integer_shift,hcoe] at heq
    exact heq


private def residueK (N ℓ s : ℕ) : Finset ℕ:=
  if s=0 then Finset.Icc 1 (N/ℓ) else if s≤N then Finset.range ((N-s)/ℓ+1) else ∅

private theorem residue_filter_image (N ℓ s : ℕ) (hp : 0<ℓ) (hs : s<ℓ) :
    (Finset.Icc 1 N).filter (fun i=>i%ℓ=s)=
      (residueK N ℓ s).image (fun k=>s+ℓ*k) := by
  classical
  by_cases hz : s=0
  · subst s
    simp only [residueK,ite_true,zero_add]
    ext i
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_image]
    constructor
    · rintro ⟨⟨hi0,hiN⟩,him⟩
      have he:=Nat.mod_add_div i ℓ
      rw [him,zero_add] at he
      refine ⟨i/ℓ,⟨?_,Nat.div_le_div_right hiN⟩,he⟩
      apply Nat.one_le_iff_ne_zero.mpr
      intro hq
      rw [hq,Nat.mul_zero] at he
      omega
    · rintro ⟨k,⟨hk0,hkN⟩,rfl⟩
      refine ⟨⟨by nlinarith,by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hkN⟩,?_⟩
      simp
  · by_cases hN : s≤N
    · simp only [residueK,if_neg hz,if_pos hN]
      ext i
      simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_image,Finset.mem_range]
      constructor
      · rintro ⟨⟨hi0,hiN⟩,him⟩
        have he:=Nat.mod_add_div i ℓ
        rw [him] at he
        have hm : ℓ*(i/ℓ)≤N-s:=by omega
        refine ⟨i/ℓ,?_,he⟩
        have hq := (Nat.le_div_iff_mul_le hp).mpr (by simpa only [Nat.mul_comm] using hm)
        omega
      · rintro ⟨k,hk,rfl⟩
        have hk' : k≤(N-s)/ℓ:=by omega
        have hm : ℓ*k≤N-s:=by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hk'
        refine ⟨⟨by omega,by omega⟩,?_⟩
        simp [Nat.add_mod,Nat.mod_eq_of_lt hs]
    · simp only [residueK,if_neg hz,if_neg hN,Finset.image_empty]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hI,hm⟩:=Finset.mem_filter.mp hi
      have hbound:=(Finset.mem_Icc.mp hI).2
      have he:=Nat.mod_add_div i ℓ
      rw [hm] at he
      omega

private theorem residueK_count (N ℓ s : ℕ) (hp : 0<ℓ) (hs : s<ℓ) :
    residueK N ℓ s=if s=0 then Finset.Icc 1 (countClass N ℓ s) else
      Finset.range (countClass N ℓ s) := by
  have hi : Function.Injective (fun k=>s+ℓ*k):=by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel h)
  have hc : countClass N ℓ s=(residueK N ℓ s).card:=by
    rw [countClass,residue_filter_image N ℓ s hp hs,Finset.card_image_of_injective _ hi]
  by_cases hz : s=0
  · simpa only [residueK,hz,ite_true,Nat.card_Icc,Nat.add_sub_cancel] using
      congrArg (fun k=>Finset.Icc 1 k) hc.symm
  · by_cases hN : s≤N
    · simpa only [residueK,if_neg hz,if_pos hN,Finset.card_range] using
        congrArg Finset.range hc.symm
    · simp only [residueK,if_neg hz,if_neg hN,Finset.card_empty] at hc ⊢
      rw [hc,Finset.range_zero]

private theorem matching_product (N ℓ s : ℕ) (hp : 0<ℓ) (hs : s<ℓ) :
    Port.Li2.matchingDiscProduct ℓ s N=
      C ((ℓ:ℚ)^(countClass N ℓ s))*
        ∏ k∈(if s=0 then Finset.Icc 1 (countClass N ℓ s) else Finset.range (countClass N ℓ s)),
          (X+C (k:ℚ)) := by
  classical
  have hi : Function.Injective (fun k=>s+ℓ*k):=by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel h)
  unfold Port.Li2.matchingDiscProduct
  rw [residue_filter_image N ℓ s hp hs,Finset.prod_image (fun a ha b hb h=>hi h)]
  have he : (∏ k∈residueK N ℓ s,(C (ℓ:ℚ)*X+C (((s+ℓ*k:ℕ):ℚ)-(s:ℚ))):ℚ[X])=
      C ((ℓ:ℚ)^((residueK N ℓ s).card))*∏ k∈residueK N ℓ s,(X+C (k:ℚ)) := by
    calc
      _=∏ k∈residueK N ℓ s,C (ℓ:ℚ)*(X+C (k:ℚ)):=by
        apply Finset.prod_congr rfl
        intro k hk
        have hc : (((s+ℓ*k:ℕ):ℚ)-(s:ℚ))=(ℓ:ℚ)*(k:ℚ):=by push_cast;ring
        rw [hc,Polynomial.C_mul]
        ring
      _=_:=by rw [Finset.prod_mul_distrib,Finset.prod_const,←map_pow]
  rw [he,residueK_count N ℓ s hp hs]
  by_cases hz : s=0 <;> simp only [hz,ite_true,ite_false,Nat.card_Icc,Nat.add_sub_cancel,Finset.card_range]

private theorem linear_prod_ne_zero (S : Finset ℕ) :
    rfPoly (∏ i∈S,(X+C (i:ℚ)))≠0 := by
  apply RatFunc.algebraMap_ne_zero
  exact Finset.prod_ne_zero_iff.mpr
    (fun (i : ℕ) (hi : i∈S)=>Polynomial.X_add_C_ne_zero (i:ℚ))

private theorem matching_weight_V (a c d : ℕ) (hac : a≤c) :
    rfPoly (∏ i∈Finset.range a,(X+C (i:ℚ)))^3/
      rfPoly (∏ i∈Finset.range c,(X+C (i:ℚ)))=weight ⟨.V,a,c,d⟩ := by
  classical
  have hs : Finset.range c=Finset.range a∪Finset.Ico a c:=by
    ext i
    simp only [Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd : Disjoint (Finset.range a) (Finset.Ico a c):=by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_range,Finset.mem_Ico] at hi hj
    omega
  have hp : (∏ i∈Finset.range c,(X+C (i:ℚ)))=
      (∏ i∈Finset.range a,(X+C (i:ℚ)))*(∏ i∈Finset.Ico a c,(X+C (i:ℚ))) := by
    rw [hs,Finset.prod_union hd]
  have hpow : (∏ i∈Finset.range a,(X+C (i:ℚ)))^2=∏ i∈Finset.range a,(X+C (i:ℚ))^2:=by rw [Finset.prod_pow]
  have hN:=linear_prod_ne_zero (Finset.range a)
  have hD:=linear_prod_ne_zero (Finset.Ico a c)
  rw [hp]
  simp only [weight,weightNum,weightDen,poleSet,rfPoly,map_mul,map_pow] at *
  rw [←hpow,map_pow]
  field_simp <;> ring

private theorem matching_weight_U (a c d : ℕ) (hac : a≤c) :
    rfPoly (∏ i∈Finset.Icc 1 a,(X+C (i:ℚ)))^3/
      rfPoly (∏ i∈Finset.Icc 1 c,(X+C (i:ℚ)))=
      (rfX:RatFunc ℚ)⁻¹*weight ⟨.U,a,c,d⟩ := by
  classical
  have hs : Finset.Icc 1 c=Finset.Icc 1 a∪Finset.Ioc a c:=by
    ext i
    simp only [Finset.mem_Icc,Finset.mem_union,Finset.mem_Ioc]
    omega
  have hd : Disjoint (Finset.Icc 1 a) (Finset.Ioc a c):=by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_Icc,Finset.mem_Ioc] at hi hj
    omega
  have hp : (∏ i∈Finset.Icc 1 c,(X+C (i:ℚ)))=
      (∏ i∈Finset.Icc 1 a,(X+C (i:ℚ)))*(∏ i∈Finset.Ioc a c,(X+C (i:ℚ))) := by
    rw [hs,Finset.prod_union hd]
  have hpow : (∏ i∈Finset.Icc 1 a,(X+C (i:ℚ)))^2=∏ i∈Finset.Icc 1 a,(X+C (i:ℚ))^2:=by rw [Finset.prod_pow]
  have hN:=linear_prod_ne_zero (Finset.Icc 1 a)
  have hD:=linear_prod_ne_zero (Finset.Ioc a c)
  have hX : rfPoly (X:ℚ[X])≠0:=RatFunc.algebraMap_ne_zero (by simp)
  rw [hp]
  simp only [weight,weightNum,weightDen,poleSet,rfPoly,rfX,map_mul,map_pow] at *
  rw [←hpow,map_pow]
  field_simp <;> ring

private def matchingCore (N ℓ : ℕ) (s : Fin ℓ) : ℚ[X]:=
  ∏ k∈(if s.val=0 then Finset.Icc 1 (countClass N ℓ s) else Finset.range (countClass N ℓ s)),(X+C (k:ℚ))

private theorem matchingCore_weight (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) (s : Fin ℓ) :
    rfPoly (matchingCore n ℓ s)^3/rfPoly (matchingCore (4*n) ℓ s)=classWeight n ℓ s := by
  have hac : a n ℓ s≤c n ℓ s:=by have h:=(class_counts n ℓ hR).1 s;omega
  by_cases hs : s.val=0
  · simpa only [matchingCore,classWeight,classKey,a,c,hs,ite_true] using
      matching_weight_U (a n ℓ s) (c n ℓ s) (m n ℓ s) hac
  · simpa only [matchingCore,classWeight,classKey,a,c,if_neg hs] using
      matching_weight_V (a n ℓ s) (c n ℓ s) (m n ℓ s) hac

private theorem field_weight_scale {K : Type*} [Field K] (x A B : K) (hx : x≠0) (a c : ℕ) :
    (x^a*A)^3/(x^c*B)=x^(3*(a:ℤ)-c)*(A^3/B) := by
  by_cases hB : B=0
  · simp [hB]
  · have he : 3*(a:ℤ)-(c:ℤ)=((3*a:ℕ):ℤ)-(c:ℤ):=by push_cast;ring
    rw [he,_root_.zpow_sub₀ hx,zpow_natCast,zpow_natCast]
    simp only [pow_mul]
    field_simp
    <;> ring

private theorem matching_disc_ratio (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) (s : Fin ℓ) :
    rfPoly (Port.Li2.matchingDiscProduct ℓ s.val n)^3/
      rfPoly (Port.Li2.matchingDiscProduct ℓ s.val (4*n))=
      (rfPoly (C (ℓ:ℚ)))^(3*(a n ℓ s:ℤ)-c n ℓ s)*classWeight n ℓ s := by
  have hp : 0<ℓ:=(Fact.out : ℓ.Prime).pos
  have hx : rfPoly (C (ℓ:ℚ))≠0:=RatFunc.algebraMap_ne_zero (by
    rw [Polynomial.C_ne_zero]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  have hc (k : ℕ) : rfPoly (C ((ℓ:ℚ)^k))=(rfPoly (C (ℓ:ℚ)))^k:=by
    unfold rfPoly
    rw [Polynomial.C_pow,map_pow]
  rw [matching_product n ℓ s.val hp s.isLt,matching_product (4*n) ℓ s.val hp s.isLt]
  change rfPoly (C ((ℓ:ℚ)^(a n ℓ s))*matchingCore n ℓ s)^3/
    rfPoly (C ((ℓ:ℚ)^(c n ℓ s))*matchingCore (4*n) ℓ s)=_
  have hm (P Q : ℚ[X]) : rfPoly (P*Q)=rfPoly P*rfPoly Q:=by exact map_mul (algebraMap ℚ[X] (RatFunc ℚ)) P Q
  rw [hm,hm,hc,hc,field_weight_scale _ _ _ hx,matchingCore_weight n ℓ hR s]

private theorem atZeroPadic_poly (ℓ : ℕ) [Fact ℓ.Prime] (P : ℚ[X]) :
    atZeroPadic ℓ (rfPoly P)=polyHahn ℓ (P.map (Rat.castHom (Padic ℓ))) := by
  rw [atZeroPadic_eq_hom,affineRFHahn_poly]
  simp only [C_1,C_0,one_mul,add_zero,comp_X]

private theorem atLocal_poly (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P : ℚ[X]) :
    atLocal (rfPoly P) ℓ s=polyHahn ℓ ((P.comp (C (ℓ:ℚ)*X-C (s:ℚ))).map (Rat.castHom (Padic ℓ))) := by
  rw [atLocal_eq_hom,affineRFHahn_poly]
  simp only [C_neg,sub_eq_add_neg]

private theorem nonmatching_disc_eq (N ℓ : ℕ) (s : Fin ℓ) :
    Port.Li2.nonmatchingDiscProduct ℓ s.val N=
      ((nonmatchingInt N ℓ s).map (Int.castRingHom ℚ)).comp (C (ℓ:ℚ)*X-C (s:ℚ)) := by
  rw [nonmatchingInt_map]
  simp only [Port.Li2.nonmatchingDiscProduct,Polynomial.prod_comp,add_comp,X_comp,C_comp]
  apply Finset.prod_congr rfl
  intro i hi
  rw [C_sub]
  ring

private theorem atLocal_D_factor (N ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) :
    atLocal (rfPoly (Port.Li2.D N)) ℓ s=
      atZeroPadic ℓ (rfPoly (Port.Li2.matchingDiscProduct ℓ s.val N))*
        atLocal (rfPoly ((nonmatchingInt N ℓ s).map (Int.castRingHom ℚ))) ℓ s := by
  rw [atLocal_poly,Port.Li2.D_disc_factorization,Polynomial.map_mul,map_mul,
    ←atZeroPadic_poly,nonmatching_disc_eq,←atLocal_poly]

private theorem atLocal_div (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (F G : RatFunc ℚ) :
    atLocal (F/G) ℓ s=atLocal F ℓ s/atLocal G ℓ s := by
  simp only [atLocal_eq_hom,map_div₀]

private theorem atLocal_pow (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (F : RatFunc ℚ) (n : ℕ) :
    atLocal (F^n) ℓ s=atLocal F ℓ s^n := by
  simp only [atLocal_eq_hom,map_pow]

private theorem atZeroPadic_div (ℓ : ℕ) [Fact ℓ.Prime] (F G : RatFunc ℚ) :
    atZeroPadic ℓ (F/G)=atZeroPadic ℓ F/atZeroPadic ℓ G := by
  simp only [atZeroPadic_eq_hom,map_div₀]

private theorem atZeroPadic_pow (ℓ : ℕ) [Fact ℓ.Prime] (F : RatFunc ℚ) (n : ℕ) :
    atZeroPadic ℓ (F^n)=atZeroPadic ℓ F^n := by
  simp only [atZeroPadic_eq_hom,map_pow]

private theorem atZeroPadic_zpow (ℓ : ℕ) [Fact ℓ.Prime] (F : RatFunc ℚ) (n : ℤ) :
    atZeroPadic ℓ (F^n)=atZeroPadic ℓ F^n := by
  simp only [atZeroPadic_eq_hom,map_zpow₀]

private theorem atZeroPadic_C (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ) :
    atZeroPadic ℓ (rfPoly (C q))=HahnSeries.C (q:Padic ℓ) := by
  rw [atZeroPadic_poly,Polynomial.map_C,polyHahn_C]
  simp only [eq_ratCast]

private theorem atLocal_W_factor (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) (s : Fin ℓ) :
    atLocal (W n) ℓ s=
      HahnSeries.C ((ℓ:Padic ℓ)^(3*(a n ℓ s:ℤ)-c n ℓ s))*atZeroPadic ℓ (classWeight n ℓ s)*
        (atLocal (rfPoly ((nonmatchingInt n ℓ s).map (Int.castRingHom ℚ))) ℓ s^3/
          atLocal (rfPoly ((nonmatchingInt (4*n) ℓ s).map (Int.castRingHom ℚ))) ℓ s) := by
  have hm:=congrArg (atZeroPadic ℓ) (matching_disc_ratio n ℓ hR s)
  simp only [atZeroPadic_div,atZeroPadic_pow,atZeroPadic_mul,atZeroPadic_zpow,
    atZeroPadic_C,Rat.cast_natCast] at hm
  rw [←map_zpow₀] at hm
  have hw : atLocal (W n) ℓ s=
      (atZeroPadic ℓ (rfPoly (Port.Li2.matchingDiscProduct ℓ s.val n))*
        atLocal (rfPoly ((nonmatchingInt n ℓ s).map (Int.castRingHom ℚ))) ℓ s)^3/
      (atZeroPadic ℓ (rfPoly (Port.Li2.matchingDiscProduct ℓ s.val (4*n)))*
        atLocal (rfPoly ((nonmatchingInt (4*n) ℓ s).map (Int.castRingHom ℚ))) ℓ s) := by
    change atLocal ((rfPoly (Port.Li2.D n))^3/rfPoly (Port.Li2.D (4*n))) ℓ s=_
    rw [atLocal_div,atLocal_pow,atLocal_D_factor,atLocal_D_factor]
  rw [hw,mul_pow,mul_div_mul_comm,hm]


private theorem crt_pair_factor (n ℓ : ℕ) (s : Fin ℓ) (P Q : Ix n ℓ) :
    crtE n ℓ P*crtE n ℓ Q=
      (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)*
        (crtTailInt n ℓ s P*crtTailInt n ℓ s Q).map (Int.castRingHom ℚ) := by
  have hp:=congrArg (Polynomial.map (Int.castRingHom ℚ)) (crtEInt_factor n ℓ s P)
  have hq:=congrArg (Polynomial.map (Int.castRingHom ℚ)) (crtEInt_factor n ℓ s Q)
  simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_X,
    Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast] at hp hq
  rw [crtE,crtE,hp,hq,pow_add,Polynomial.map_mul]
  ring

private theorem atLocal_linear (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) :
    atLocal (rfPoly (X+C (s:ℚ))) ℓ s=HahnSeries.C (ℓ:Padic ℓ)*hX := by
  rw [atLocal_poly]
  have he : (X+C (s:ℚ)).comp (C (ℓ:ℚ)*X-C (s:ℚ))=C (ℓ:ℚ)*X:=by
    simp only [add_comp,X_comp,C_comp]
    ring
  rw [he]
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,map_mul,
    polyHahn_C,polyHahn_X,eq_ratCast,Rat.cast_natCast]

private theorem atLocal_crt_pair (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P Q : Ix n ℓ) :
    atLocal (rfPoly (crtE n ℓ P*crtE n ℓ Q)) ℓ s=
      (HahnSeries.C (ℓ:Padic ℓ)*hX)^(d n ℓ s P+d n ℓ s Q)*
        atLocal (rfPoly ((crtTailInt n ℓ s P*crtTailInt n ℓ s Q).map (Int.castRingHom ℚ))) ℓ s := by
  rw [crt_pair_factor]
  have hm (P Q : ℚ[X]) : rfPoly (P*Q)=rfPoly P*rfPoly Q:=by exact map_mul (algebraMap ℚ[X] (RatFunc ℚ)) P Q
  have hp (P : ℚ[X]) (d : ℕ) : rfPoly (P^d)=rfPoly P^d:=by exact map_pow (algebraMap ℚ[X] (RatFunc ℚ)) P d
  rw [hm,hp,atLocal_mul,atLocal_pow,atLocal_linear]

private theorem atZeroPadic_rfX (ℓ : ℕ) [Fact ℓ.Prime] :
    atZeroPadic ℓ rfX=hX := by
  change atZeroPadic ℓ (rfPoly X)=_
  rw [atZeroPadic_poly,Polynomial.map_X,polyHahn_X]

private theorem nonmatching_local_ne_zero (N ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) :
    atLocal (rfPoly ((nonmatchingInt N ℓ s).map (Int.castRingHom ℚ))) ℓ s≠0 := by
  rw [atLocal_eq_hom]
  have hn : rfPoly ((nonmatchingInt N ℓ s).map (Int.castRingHom ℚ))≠0:=by
    rw [nonmatchingInt_map]
    exact linear_prod_ne_zero _
  simpa only [map_zero] using
    (affineRFHahn ℓ (-(s:ℚ)) (ℓ:ℚ) (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)).injective.ne hn


private theorem local_factorization_value (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s : Fin ℓ) (P Q : Ix n ℓ) (Ψ : Germ ℓ)
    (heq : HahnSeries.C (kappa n ℓ s)*germSeries ℓ Ψ*
        atLocal (rfPoly ((nonmatchingInt (4*n) ℓ s).map (Int.castRingHom ℚ))) ℓ s=
      atLocal (rfPoly ((nonmatchingInt n ℓ s).map (Int.castRingHom ℚ))) ℓ s^3*
        atLocal (rfPoly ((crtTailInt n ℓ s P*crtTailInt n ℓ s Q).map (Int.castRingHom ℚ))) ℓ s) :
    atLocal (pairRF n ℓ P Q) ℓ s=
      HahnSeries.C ((ℓ:Padic ℓ)^((3*(a n ℓ s:ℤ)-c n ℓ s)+((d n ℓ s P+d n ℓ s Q:ℕ):ℤ))*kappa n ℓ s)*
        atZeroPadic ℓ (rfX^(d n ℓ s P+d n ℓ s Q)*classWeight n ℓ s)*germSeries ℓ Ψ := by
  let N:=atLocal (rfPoly ((nonmatchingInt n ℓ s).map (Int.castRingHom ℚ))) ℓ s
  let D:=atLocal (rfPoly ((nonmatchingInt (4*n) ℓ s).map (Int.castRingHom ℚ))) ℓ s
  let C:=atLocal (rfPoly ((crtTailInt n ℓ s P*crtTailInt n ℓ s Q).map (Int.castRingHom ℚ))) ℓ s
  let t:=d n ℓ s P+d n ℓ s Q
  let e : ℤ:=3*(a n ℓ s:ℤ)-c n ℓ s
  have hD : D≠0:=nonmatching_local_ne_zero (4*n) ℓ s
  change HahnSeries.C (kappa n ℓ s)*germSeries ℓ Ψ*D=N^3*C at heq
  have hf : N^3/D*C=HahnSeries.C (kappa n ℓ s)*germSeries ℓ Ψ := by
    calc
      _=(N^3*C)/D:=by ring
      _=_:=((eq_div_iff hD).mpr heq).symm
  have hl : atLocal (pairRF n ℓ P Q) ℓ s=
      HahnSeries.C ((ℓ:Padic ℓ)^e)*atZeroPadic ℓ (classWeight n ℓ s)*(N^3/D)*
        ((HahnSeries.C (ℓ:Padic ℓ)*hX)^t*C) := by
    rw [pairRF,atLocal_mul,atLocal_W_factor n ℓ hR s,atLocal_crt_pair]
  have hn : (HahnSeries.C (ℓ:Padic ℓ)*hX)^t=HahnSeries.C ((ℓ:Padic ℓ)^t)*hX^t:=by
    rw [mul_pow,←map_pow]
  have hs : atZeroPadic ℓ (rfX^t*classWeight n ℓ s)=hX^t*atZeroPadic ℓ (classWeight n ℓ s):=by
    rw [atZeroPadic_mul,atZeroPadic_pow,atZeroPadic_rfX]
  have hp : (ℓ:Padic ℓ)≠0:=by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hc : (HahnSeries.C ((ℓ:Padic ℓ)^e):HahnSeries ℤ (Padic ℓ))*HahnSeries.C ((ℓ:Padic ℓ)^t)*HahnSeries.C (kappa n ℓ s)=
      HahnSeries.C ((ℓ:Padic ℓ)^(e+(t:ℤ))*kappa n ℓ s) := by
    rw [←map_mul,←map_mul]
    congr 1
    rw [_root_.zpow_add₀ hp,zpow_natCast]
  rw [hl,hn]
  calc
    _=HahnSeries.C ((ℓ:Padic ℓ)^e)*HahnSeries.C ((ℓ:Padic ℓ)^t)*
        (hX^t*atZeroPadic ℓ (classWeight n ℓ s))*(N^3/D*C):=by ring
    _=HahnSeries.C ((ℓ:Padic ℓ)^e)*HahnSeries.C ((ℓ:Padic ℓ)^t)*
        (hX^t*atZeroPadic ℓ (classWeight n ℓ s))*(HahnSeries.C (kappa n ℓ s)*germSeries ℓ Ψ):=by rw [hf]
    _=(HahnSeries.C ((ℓ:Padic ℓ)^e)*HahnSeries.C ((ℓ:Padic ℓ)^t)*HahnSeries.C (kappa n ℓ s))*
        (hX^t*atZeroPadic ℓ (classWeight n ℓ s))*germSeries ℓ Ψ:=by ring
    _=_:=by rw [hc,←hs]

theorem local_factorization (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s : Fin ℓ) (P Q : Ix n ℓ) :
    ∃ Ψ : Germ ℓ,IsUnit (Ψ 0) ∧ Unit ℓ (kappa n ℓ s) ∧
      atLocal (W n*rfPoly (crtE n ℓ P*crtE n ℓ Q)) ℓ s=
        HahnSeries.single 0 ((ℓ:Padic ℓ)^((3*(a n ℓ s:ℤ)-c n ℓ s)+
          d n ℓ s P+d n ℓ s Q)*kappa n ℓ s)*
          atZeroPadic ℓ (rfX^(d n ℓ s P+d n ℓ s Q)*classWeight n ℓ s)*germSeries ℓ Ψ ∧
      (Ψ 0:Padic ℓ)=
        (((crtE n ℓ P*crtE n ℓ Q /ₘ
          (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)).eval (-(s:ℚ)):ℚ):Padic ℓ) := by
  obtain ⟨Ψ,hunit,hzero,heq⟩:=nonsingular_germ n ℓ s P Q
  refine ⟨Ψ,hunit,kappa_unit n ℓ s,?_,?_⟩
  · have he:=local_factorization_value n ℓ hR s P Q Ψ heq
    simpa only [pairRF,Nat.cast_add,add_assoc,HahnSeries.C_apply] using he
  · rw [crt_pair_quotient,show -(s:ℚ)=((-(s.val:ℤ):ℤ):ℚ) by simp,
      Polynomial.eval_intCast_map]
    simpa only [Int.coe_castRingHom,Rat.cast_intCast] using! hzero


private theorem crtPiInt_last_factor (n ℓ : ℕ) (s : Fin ℓ) (P : Ix n ℓ)
    (hs : s≠P.1) (hlast : P.2.val+1=m n ℓ P.1) :
    crtPiInt n ℓ s=(X+C (P.1.val:ℤ))*crtTailInt n ℓ s P := by
  classical
  have herase : (Finset.univ.erase s).erase P.1=(Finset.univ.erase P.1).erase s:=by
    ext t
    simp only [Finset.mem_erase,Finset.mem_univ]
    tauto
  have hm : P.1∈Finset.univ.erase s:=by simp [Ne.symm hs]
  have he : (∏ t∈Finset.univ.erase s,(X+C (t.val:ℤ))^(m n ℓ t))=
      (X+C (P.1.val:ℤ))^(m n ℓ P.1)*
        ∏ t∈(Finset.univ.erase s).erase P.1,(X+C (t.val:ℤ))^(m n ℓ t):=
    (Finset.mul_prod_erase (Finset.univ.erase s)
      (fun t : Fin ℓ=>(X+C (t.val:ℤ))^(m n ℓ t)) hm).symm
  unfold crtPiInt
  rw [he,←hlast,pow_succ]
  simp only [crtTailInt,if_neg hs,herase]
  ring

private theorem crtTail_last_eval (n ℓ : ℕ) (s : Fin ℓ) (P : Ix n ℓ)
    (hs : s≠P.1) (hlast : P.2.val+1=m n ℓ P.1) :
    ((crtTailInt n ℓ s P).map (Int.castRingHom ℚ)).eval (-(s:ℚ))=
      (crtPi n ℓ s).eval (-(s:ℚ))/((P.1:ℚ)-(s:ℚ)) := by
  have he:=congrArg (fun R : ℤ[X]=> (R.map (Int.castRingHom ℚ)).eval (-(s:ℚ)))
    (crtPiInt_last_factor n ℓ s P hs hlast)
  simp only [Polynomial.map_mul,Polynomial.map_add,Polynomial.map_X,Polynomial.map_C,
    Int.coe_castRingHom,Int.cast_natCast,eval_mul,eval_add,eval_X,eval_C] at he
  have hd : (P.1:ℚ)-(s:ℚ)≠0:=by
    intro h
    have hv : P.1.val=s.val:=by exact_mod_cast sub_eq_zero.mp h
    exact hs (Fin.ext hv.symm)
  apply (eq_div_iff hd).mpr
  change _=((crtPiInt n ℓ s).map (Int.castRingHom ℚ)).eval (-(s:ℚ))
  rw [he]
  ring

private theorem same_pair_constant (n ℓ : ℕ) (s : Fin ℓ) (P Q : Ix n ℓ)
    (hP : P.1=s) (hQ : Q.1=s) :
    (crtE n ℓ P*crtE n ℓ Q /ₘ (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)).eval (-(s:ℚ))=
      (crtPi n ℓ s).eval (-(s:ℚ))^2 := by
  rw [crt_pair_quotient]
  have hp : crtTailInt n ℓ s P=crtPiInt n ℓ s:=by simp only [crtTailInt,hP,ite_true]
  have hq : crtTailInt n ℓ s Q=crtPiInt n ℓ s:=by simp only [crtTailInt,hQ,ite_true]
  rw [hp,hq,Polynomial.map_mul,eval_mul]
  change (crtPi n ℓ s).eval (-(s:ℚ))*(crtPi n ℓ s).eval (-(s:ℚ))=_
  ring

private theorem mixed_last_constant (n ℓ : ℕ) (s : Fin ℓ) (P Q : Ix n ℓ)
    (hP : P.1=s) (hQ : s≠Q.1) (hlast : Q.2.val+1=m n ℓ Q.1) :
    (crtE n ℓ P*crtE n ℓ Q /ₘ (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)).eval (-(s:ℚ))=
      (crtPi n ℓ s).eval (-(s:ℚ))^2/((Q.1:ℚ)-(s:ℚ)) := by
  rw [crt_pair_quotient,Polynomial.map_mul,eval_mul,crtTail_last_eval n ℓ s Q hQ hlast]
  have hp : crtTailInt n ℓ s P=crtPiInt n ℓ s:=by simp only [crtTailInt,hP,ite_true]
  rw [hp]
  change (crtPi n ℓ s).eval (-(s:ℚ))*((crtPi n ℓ s).eval (-(s:ℚ))/((Q.1:ℚ)-(s:ℚ)))=_
  ring

private theorem both_last_constant (n ℓ : ℕ) (s : Fin ℓ) (P Q : Ix n ℓ)
    (hP : s≠P.1) (hQ : s≠Q.1)
    (hPlast : P.2.val+1=m n ℓ P.1) (hQlast : Q.2.val+1=m n ℓ Q.1) :
    (crtE n ℓ P*crtE n ℓ Q /ₘ (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)).eval (-(s:ℚ))=
      (crtPi n ℓ s).eval (-(s:ℚ))^2/(((P.1:ℚ)-(s:ℚ))*((Q.1:ℚ)-(s:ℚ))) := by
  rw [crt_pair_quotient,Polynomial.map_mul,eval_mul,crtTail_last_eval n ℓ s P hP hPlast,
    crtTail_last_eval n ℓ s Q hQ hQlast]
  simp only [div_eq_mul_inv,mul_inv]
  ring


private theorem atLocal_poly_series (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P : ℚ[X]) :
    atLocal (rfPoly P) ℓ s=HahnSeries.ofPowerSeries ℤ (Padic ℓ)
      (Port.Li2.rationalPolynomialSeries (P.comp (C (ℓ:ℚ)*X-C (s:ℚ)))) := by
  rw [atLocal_poly]
  rfl

private theorem local_cleared_series (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ)
    (M : ℕ) (P : ℚ[X]) (scale : Padic ℓ) (hscale : scale≠0)
    (f : PowerSeries (PadicInt ℓ)) (r : Fin ℓ→PadicInt ℓ)
    (he : atLocal (rfPoly P/rfPoly (Port.Li2.D M)) ℓ s*
      integralHahnHom ℓ (Port.Li2.integralPoleDenominator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)):PowerSeries (PadicInt ℓ))=
      HahnSeries.C scale*integralHahnHom ℓ (Port.Li2.integralPoleNumerator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)) f r)) :
    Port.Li2.primeDiscPolynomialSeries s.val M *
      PowerSeries.map (algebraMap (PadicInt ℓ) (Padic ℓ))
        (Port.Li2.integralPoleNumerator Port.Unified.Proofs.Hermite.generalPoleCenters f r)=
      PowerSeries.C scale⁻¹*
        (Port.Li2.fieldPoleDenominator (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)):PowerSeries (Padic ℓ))*
        Port.Li2.rationalPolynomialSeries (P.comp (C (ℓ:ℚ)*X-C (s:ℚ))) := by
  classical
  let centers:=Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)
  have hd : atLocal (rfPoly (Port.Li2.D M)) ℓ s≠0:=by
    rw [atLocal_eq_hom]
    simpa only [rfPoly,map_zero] using (affineRFHahn ℓ (-(s:ℚ)) (ℓ:ℚ)
      (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)).injective.ne
        (RatFunc.algebraMap_ne_zero (Port.Li2.D_monic M).ne_zero)
  have hc : (HahnSeries.C scale:HahnSeries ℤ (Padic ℓ))≠0:=by
    simpa only [map_zero] using (HahnSeries.C_injective (Γ:=ℤ)).ne hscale
  have hden : integralHahnHom ℓ (Port.Li2.integralPoleDenominator centers:PowerSeries (PadicInt ℓ))=
      HahnSeries.ofPowerSeries ℤ (Padic ℓ) (Port.Li2.fieldPoleDenominator centers:PowerSeries (Padic ℓ)) := by
    rw [integralHahnHom_poly]
    change polyHahn ℓ ((Port.Li2.integralPoleDenominator centers).map (algebraMap (PadicInt ℓ) (Padic ℓ)))=_
    rw [Port.Li2.fieldPoleDenominator_map]
    rfl
  have he' : atLocal (rfPoly P) ℓ s*
      integralHahnHom ℓ (Port.Li2.integralPoleDenominator centers:PowerSeries (PadicInt ℓ))=
      HahnSeries.C scale*integralHahnHom ℓ (Port.Li2.integralPoleNumerator centers f r)*
        atLocal (rfPoly (Port.Li2.D M)) ℓ s:=by
    apply (div_eq_iff hd).mp
    rw [mul_div_right_comm]
    simpa only [atLocal_eq_hom,map_div₀] using he
  apply HahnSeries.ofPowerSeries_injective (Γ:=ℤ) (R:=Padic ℓ)
  simp only [map_mul,HahnSeries.ofPowerSeries_C]
  rw [Port.Li2.primeDiscPolynomialSeries,←atLocal_poly_series,←atLocal_poly_series]
  change atLocal (rfPoly (Port.Li2.D M)) ℓ s*
      integralHahnHom ℓ (Port.Li2.integralPoleNumerator centers f r)=
    HahnSeries.C scale⁻¹*HahnSeries.ofPowerSeries ℤ (Padic ℓ)
      (Port.Li2.fieldPoleDenominator centers:PowerSeries (Padic ℓ))*atLocal (rfPoly P) ℓ s
  rw [←hden,map_inv₀]
  field_simp [hc]
  linear_combination -he'

private theorem rational_unit_of_norm (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ)
    (hq : Unit ℓ (q:Padic ℓ)) : q≠0 ∧ padicValRat ℓ q=0 := by
  have hn : (q:Padic ℓ)≠0:=by
    intro h
    have hh:=hq
    simp only [Unit,h,norm_zero] at hh
    exact zero_ne_one hh
  refine ⟨by exact_mod_cast hn,?_⟩
  have hp : (1:ℝ)<ℓ:=by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hv:=Padic.norm_eq_zpow_neg_valuation hn
  rw [Padic.valuation_ratCast,hq] at hv
  have he : -(padicValRat ℓ q)=0:=(zpow_right_strictMono₀ hp).injective
    (hv.symm.trans (zpow_zero (ℓ:ℝ)).symm)
  exact neg_eq_zero.mp he

private theorem parameter_hypotheses (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) :
    z≠0 ∧ Port.Li2.VG ℓ (z^ℓ) 0 ∧ Port.Li2.VG ℓ (z^ℓ/(1-z^ℓ)) 0 ∧ z^ℓ≠1 :=
  Port.Unified.Proofs.Hermite.parameterPoleHypotheses_of_hunit z
    ⟨rational_unit_of_norm ℓ z hz,rational_unit_of_norm ℓ (1-z) h1⟩

private theorem S_eq_integral (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (H : Germ ℓ) :
    S z ℓ H=(Port.Li2.restrictedMoment
      (Port.Li2.integralParameterMoment (z^ℓ) (parameter_hypotheses z ℓ hz h1).2.2.1)
      (germScaled ℓ H):Padic ℓ) := by
  have hh:=(Port.Li2.restrictedMoment_summable
    (Port.Li2.integralParameterMoment (z^ℓ) (parameter_hypotheses z ℓ hz h1).2.2.1)
    (germScaled ℓ H) (germScaled_restricted ℓ H)).map_tsum
    PadicInt.Coe.ringHom PadicInt.isOpenEmbedding_coe.continuous
  simp_rw [S,liNeg_eq_parameterMoment (z^ℓ) (parameter_hypotheses z ℓ hz h1).2.2.2]
  simpa only [S,Port.Li2.restrictedMoment,germScaled,PowerSeries.coeff_mk,
    PadicInt.Coe.ringHom_apply,map_mul,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_natCast,
    Port.Li2.integralParameterMoment,Port.Li2.integralRational] using! hh.symm


private theorem E_eq_S_eta (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ)
    (u : (PadicInt ℓ)ˣ) (hu : ((u:PadicInt ℓ):Padic ℓ)=(c:Padic ℓ)) :
    E z ℓ c=S z ℓ (etaUnit ℓ u) := by
  have hinv : (((u⁻¹:(PadicInt ℓ)ˣ):PadicInt ℓ):Padic ℓ)=(c:Padic ℓ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←hu,←PadicInt.coe_mul]
    simp
  unfold E S
  apply tsum_congr
  intro j
  simp only [etaUnit,PadicInt.coe_mul,PadicInt.coe_add,PadicInt.coe_natCast,
    PadicInt.coe_neg,PadicInt.coe_one,PadicInt.coe_pow,hinv]
  rw [show -(j:ℤ)-2=-((j+2:ℕ):ℤ) by omega,_root_.zpow_neg,zpow_natCast,inv_pow,neg_pow]
  ring

private theorem etaScaled_eq_inverse (ℓ : ℕ) [Fact ℓ.Prime] (u : (PadicInt ℓ)ˣ) :
    germScaled ℓ (etaUnit ℓ u)=Port.Li2.affineInverseSeries u (ℓ:PadicInt ℓ) 2 := by
  apply PowerSeries.ext
  intro j
  simp only [germScaled,PowerSeries.coeff_mk,Port.Li2.affineInverseSeries,
    PowerSeries.coeff_C_mul,Port.Li2.inverseOneSubSeries,PowerSeries.coeff_rescale]
  simp only [PowerSeries.invOneSubPow,PowerSeries.coeff_mk]
  simp only [Nat.reduceAdd,Nat.add_sub_cancel,Nat.choose_one_right,Nat.cast_add,Nat.cast_one,
    etaUnit]
  rw [mul_pow (-(ℓ:PadicInt ℓ)),neg_pow (ℓ:PadicInt ℓ) j,pow_add]
  ring

private theorem E_eq_reciprocal (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (c : ℤ) (hc0 : (c:ℚ)≠0) (hcv : padicValRat ℓ (c:ℚ)=0) :
    E z ℓ c=(Port.Li2.padicParameterG (z^ℓ)
      (parameter_hypotheses z ℓ hz h1).2.2.1
      (Port.Li2.padicReciprocalSeries (c:ℚ) hc0 hcv 2):Padic ℓ) := by
  let u : (PadicInt ℓ)ˣ:=Port.Li2.integralRationalUnit (c:ℚ) hc0 hcv
  have hu : ((u:PadicInt ℓ):Padic ℓ)=(c:Padic ℓ):=by
    simp only [u,Port.Li2.integralRationalUnit_coe,Rat.cast_intCast]
  rw [E_eq_S_eta z ℓ c u hu,S_eq_integral z ℓ hz h1,etaScaled_eq_inverse]
  rfl


private theorem pulled_pole_nonmatching (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (s : Fin ℓ) (j : ℕ) (hn : j%ℓ≠s.val) (ξ : Padic ℓ) :
    Port.Unified.Proofs.Hermite.parameterPulledSimplePole z
      (parameter_hypotheses z ℓ hz h1).2.2.1 ((ℓ:Padic ℓ)^2*ξ) j s=
      (j:Padic ℓ)*E z ℓ ((j:ℤ)-s.val) := by
  have hp:=(Fact.out : ℓ.Prime).pos
  have hnot : ¬ℓ∣j+(ℓ-1-s.val)+1:=by
    intro he
    apply hn
    exact (Port.Unified.Proofs.Hermite.matching_shift_dvd_iff ℓ j s).1 he
  have hunit:=Port.Li2.rational_nonmultiple_sub_prime (p:=ℓ) (j+(ℓ-1-s.val)+1) hnot
  have he : (((j+(ℓ-1-s.val)+1:ℕ):ℚ)-(ℓ:ℚ))=(((j:ℤ)-s.val:ℤ):ℚ):=by
    have ht:=Port.Li2.polePullback_denominator (p:=ℓ) j s.val s.isLt
    push_cast at ht ⊢
    linear_combination ht
  have hc0 : (((j:ℤ)-s.val:ℤ):ℚ)≠0:=by rw [←he];exact hunit.1
  have hcv : padicValRat ℓ (((j:ℤ)-s.val:ℤ):ℚ)=0:=by rw [←he];exact hunit.2
  unfold Port.Unified.Proofs.Hermite.parameterPulledSimplePole
  rw [Port.Unified.Proofs.Hermite.parameterDissectedSquare_nonmatching _ _ _ _ hnot,
    E_eq_reciprocal z ℓ hz h1 _ hc0 hcv]
  congr 4

private theorem pulled_pole_matching (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (s : Fin ℓ) (j : ℕ) (hm : j%ℓ=s.val) (ξ : Padic ℓ) :
    (z:Padic ℓ)^(-(s.val:ℤ))*
      Port.Unified.Proofs.Hermite.parameterPulledSimplePole z
        (parameter_hypotheses z ℓ hz h1).2.2.1 ((ℓ:Padic ℓ)^2*ξ) j s=
      (j:Padic ℓ)*(z:Padic ℓ)^(-(j:ℤ))/(ℓ:Padic ℓ)^2*
        ((ℓ:Padic ℓ)^2*ξ-(tauK (z^ℓ) (j/ℓ):ℚ)) := by
  have hp:=(Fact.out : ℓ.Prime).pos
  have hzne : (z:Padic ℓ)≠0:=by
    exact_mod_cast (parameter_hypotheses z ℓ hz h1).1
  have hdiv:=(Port.Unified.Proofs.Hermite.matching_shift_dvd_iff ℓ j s).2 hm
  have hind : ℓ*(j/ℓ)+s.val=j:=by
    have he:=Nat.mod_add_div j ℓ
    omega
  have hb : j+(ℓ-1-s.val)+1=ℓ*(j/ℓ+1):=by
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hk : ((j+(ℓ-1-s.val)+1)/ℓ-1:ℕ)=(j/ℓ:ℕ):=by
    rw [hb,Nat.mul_comm ℓ (j/ℓ+1),Nat.mul_div_left _ hp]
    exact Nat.add_sub_cancel (j/ℓ) 1
  have hpow : (((z^ℓ)^(-((j/ℓ:ℕ):ℤ)):ℚ):Padic ℓ)=
      (z:Padic ℓ)^(-((ℓ*(j/ℓ):ℕ):ℤ)) := by
    push_cast
    rw [←zpow_natCast,←zpow_mul]
    congr 1
    push_cast
    ring
  have hexp : (z:Padic ℓ)^(-(s.val:ℤ))*
      (((z^ℓ)^(-((j/ℓ:ℕ):ℤ)):ℚ):Padic ℓ)=(z:Padic ℓ)^(-(j:ℤ)):=by
    rw [hpow,←_root_.zpow_add₀ hzne]
    congr 1
    have he : ((ℓ*(j/ℓ):ℕ):ℤ)+(s.val:ℤ)=(j:ℤ):=by exact_mod_cast hind
    omega
  unfold Port.Unified.Proofs.Hermite.parameterPulledSimplePole
  rw [Port.Unified.Proofs.Hermite.parameterDissectedSquare_matching _ _ _ _ hdiv,hk]
  have hpow' : ((z^ℓ:ℚ):Padic ℓ)⁻¹^(j/ℓ)=
      (((z^ℓ)^(-((j/ℓ:ℕ):ℤ)):ℚ):Padic ℓ):=by
    simp only [_root_.zpow_neg,zpow_natCast,Rat.cast_inv,Rat.cast_pow,inv_pow]
  rw [hpow']
  change _= (j:Padic ℓ)*(z:Padic ℓ)^(-(j:ℤ))/(ℓ:Padic ℓ)^2*
    ((ℓ:Padic ℓ)^2*ξ-(Port.Li2.parameterTau (z^ℓ) (j/ℓ):ℚ))
  rw [show (z:Padic ℓ)^(-(j:ℤ))=(z:Padic ℓ)^(-(s.val:ℤ))*
    (((z^ℓ)^(-((j/ℓ:ℕ):ℤ)):ℚ):Padic ℓ) from hexp.symm]
  simp only [div_eq_mul_inv,inv_pow]
  ring

private theorem polynomial_li_sum (w : ℚ) (hw : w≠1) (P : ℚ[X]) :
    (∑i∈Finset.range (P.natDegree+1),P.coeff i*liNeg i w)=Port.Li2.parameterG w P := by
  simp_rw [liNeg_eq_parameterMoment w hw]
  unfold Port.Li2.parameterG
  exact (P.sum_over_range (f:=fun n a=>a*Port.Li2.parameterMoment w n) (fun n=>by simp)).symm

private theorem local_polynomial_pulled (w : ℚ) (hw : w≠1)
    (ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ) (P : ℚ[X]) :
    (∑i∈Finset.range (((X*P).derivative.comp (C (-(s:ℚ))+C (ℓ:ℚ)*X)).natDegree+1),
      (((X*P).derivative.comp (C (-(s:ℚ))+C (ℓ:ℚ)*X)).coeff i:Padic ℓ)*(liNeg i w:ℚ))=
    (Port.Li2.parameterU w (P.comp (C (ℓ:ℚ)*X-C (s:ℚ))):ℚ)-
      (s:Padic ℓ)/(ℓ:Padic ℓ)*(Port.Li2.parameterV w (P.comp (C (ℓ:ℚ)*X-C (s:ℚ))):ℚ) := by
  have hp : (ℓ:ℚ)≠0:=by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have ha : C (-(s:ℚ))+C (ℓ:ℚ)*X=C (ℓ:ℚ)*X-C (s:ℚ):=by simp [sub_eq_add_neg,add_comm]
  rw [ha]
  have hs:=polynomial_li_sum w hw ((X*P).derivative.comp (C (ℓ:ℚ)*X-C (s:ℚ)))
  have hc:=congrArg (fun q : ℚ=>(q:Padic ℓ)) hs
  simp only [Rat.cast_sum,Rat.cast_mul] at hc
  rw [hc,Port.Li2.affine_differential_identity _ _ hp,Port.Li2.parameterG_sub,
    Port.Li2.parameterG_C_mul,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast]
  rfl

private theorem localClass_canonical (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (s : Fin ℓ) (ξ : Padic ℓ) (F : RatFunc ℚ) :
    localClass z ℓ s ξ F=(z:Padic ℓ)^(-(s.val:ℤ))*
      (((Port.Li2.parameterU (z^ℓ) ((pp F).comp (C (ℓ:ℚ)*X-C (s:ℚ)))):ℚ)-
        (s:Padic ℓ)/(ℓ:Padic ℓ)*(Port.Li2.parameterV (z^ℓ)
          ((pp F).comp (C (ℓ:ℚ)*X-C (s:ℚ))):ℚ)+
        ∑j∈poleIndices F,(poleRes F j:Padic ℓ)*
          Port.Unified.Proofs.Hermite.parameterPulledSimplePole z
            (parameter_hypotheses z ℓ hz h1).2.2.1 ((ℓ:Padic ℓ)^2*ξ) j s) := by
  classical
  unfold localClass
  rw [local_polynomial_pulled _ (parameter_hypotheses z ℓ hz h1).2.2.2,
    mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hm : j%ℓ=s.val
  · rw [if_pos hm]
    have he:=pulled_pole_matching z ℓ hz h1 s j hm ξ
    linear_combination -(poleRes F j:Padic ℓ)*he
  · rw [if_neg hm,pulled_pole_nonmatching z ℓ hz h1 s j hm ξ]
    ring

private theorem localClass_pulled_fraction (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (s : Fin ℓ) (ξ : Padic ℓ) (M : ℕ) (P : ℚ[X]) :
    localClass z ℓ s ξ (rfPoly P/rfPoly (Port.Li2.D M))=
      (z:Padic ℓ)^(-(s.val:ℤ))*Port.Unified.Proofs.Hermite.parameterPulledValue z
        (parameter_hypotheses z ℓ hz h1).2.2.1 ((ℓ:Padic ℓ)^2*ξ) M P s := by
  classical
  rw [localClass_canonical z ℓ hz h1 s ξ]
  let φ : ℚ[X]→Padic ℓ:=fun Q=>(Port.Li2.parameterU (z^ℓ)
    (Q.comp (C (ℓ:ℚ)*X-C (s:ℚ))):ℚ)-
      (s:Padic ℓ)/(ℓ:Padic ℓ)*(Port.Li2.parameterV (z^ℓ)
        (Q.comp (C (ℓ:ℚ)*X-C (s:ℚ))):ℚ)
  let ψ : ℕ→Padic ℓ:=fun j=>Port.Unified.Proofs.Hermite.parameterPulledSimplePole z
    (parameter_hypotheses z ℓ hz h1).2.2.1 ((ℓ:Padic ℓ)^2*ξ) j s
  have hD : Port.Li2.D M=poleProd (Finset.Icc 1 M):=rfl
  rw [hD]
  change (z:Padic ℓ)^(-(s.val:ℤ))*(φ (pp _)+∑j∈poleIndices _,(poleRes _ j:Padic ℓ)*ψ j)=_
  rw [canonical_functional ℓ P (Finset.Icc 1 M) φ ψ]
  unfold Port.Unified.Proofs.Hermite.parameterPulledValue
  rw [hD]
  congr 1
  change φ (P /ₘ poleProd (Finset.Icc 1 M)) + _=φ (P /ₘ poleProd (Finset.Icc 1 M)) + _
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [poleCoeff,denominator_derivative _ _ hj]


private theorem localClass_integral_operator (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (s : Fin ℓ) (ξ : Padic ℓ) (M : ℕ) (hM : M<ℓ*ℓ) (P : ℚ[X])
    (scale : Padic ℓ) (hscale : scale≠0)
    (f : PowerSeries (PadicInt ℓ)) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin ℓ→PadicInt ℓ)
    (he : atLocal (rfPoly P/rfPoly (Port.Li2.D M)) ℓ s*
      integralHahnHom ℓ (Port.Li2.integralPoleDenominator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)):PowerSeries (PadicInt ℓ))=
      HahnSeries.C scale*integralHahnHom ℓ (Port.Li2.integralPoleNumerator
        (Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)) f r)) :
    let hu : z^ℓ≠0∧padicValRat ℓ (z^ℓ)=0:=rational_unit_of_norm ℓ (z^ℓ)
      (by change ‖((z^ℓ:ℚ):Padic ℓ)‖=1;rw [Rat.cast_pow,norm_pow,hz,one_pow])
    let hreg:=(parameter_hypotheses z ℓ hz h1).2.2.1
    localClass z ℓ s ξ (rfPoly P/rfPoly (Port.Li2.D M))=
      (z:Padic ℓ)^(-(s.val:ℤ))*scale*
        ((Port.Unified.Proofs.Hermite.generalPoleU (z^ℓ) hu hreg f r).eval₂
          (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)-
          (s:Padic ℓ)/(ℓ:Padic ℓ)*
          (Port.Unified.Proofs.Hermite.generalPoleV (z^ℓ) hu hreg f r).eval₂
            (algebraMap (PadicInt ℓ) (Padic ℓ)) ((ℓ:Padic ℓ)^2*ξ)) := by
  intro hu hreg
  have hp:=Port.Unified.Proofs.Hermite.parameterPulledValue_integral_of_cleared z hu hreg
    ((ℓ:Padic ℓ)^2*ξ) M hM P s scale⁻¹ f hf r
      (local_cleared_series ℓ s M P scale hscale f r he)
  have hp':=congrArg (fun x : Padic ℓ=>scale*x) hp
  rw [←mul_assoc,mul_inv_cancel₀ hscale,one_mul] at hp'
  rw [localClass_pulled_fraction z ℓ hz h1 s ξ M P,hp']
  ring


private theorem germSeries_integralHahn (ℓ : ℕ) [Fact ℓ.Prime] (Ψ : Germ ℓ) :
    germSeries ℓ Ψ=integralHahnHom ℓ (germScaled ℓ Ψ) := by
  unfold germSeries integralHahnHom
  simp only [RingHom.comp_apply]
  congr 1
private theorem pairRF_fraction (n ℓ : ℕ) (P Q : Ix n ℓ) :
    pairRF n ℓ P Q=rfPoly ((Port.Li2.D n)^3*(crtE n ℓ P*crtE n ℓ Q))/rfPoly (Port.Li2.D (4*n)) := by
  unfold pairRF W rfPoly
  simp only [map_mul,map_pow]
  ring
private theorem localClass_factor_series (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (P Q : Ix n ℓ) (Ψ : Germ ℓ)
    (hfact : atLocal (pairRF n ℓ P Q) ℓ s=
      HahnSeries.C ((ℓ:Padic ℓ)^((3*(a n ℓ s:ℤ)-c n ℓ s)+((d n ℓ s P+d n ℓ s Q:ℕ):ℤ))*kappa n ℓ s)*
        atZeroPadic ℓ (rfX^(d n ℓ s P+d n ℓ s Q)*classWeight n ℓ s)*germSeries ℓ Ψ)
    (ξ : Padic ℓ) (y : PadicInt ℓ) (hy : (y:Padic ℓ)=(ℓ:Padic ℓ)^2*ξ) :
    localClass z ℓ s ξ (pairRF n ℓ P Q)=
      (z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s*
        (ℓ:Padic ℓ)^(nu n ℓ s+d n ℓ s P+d n ℓ s Q)*
        ∑'j,(ℓ:Padic ℓ)^j*(chi ℓ s Ψ j:Padic ℓ)*
          localV z ℓ ξ (rfX^(d n ℓ s P+d n ℓ s Q+(if s.val=0 then 1 else 0)+j)*classWeight n ℓ s) := by
  let D:=d n ℓ s P+d n ℓ s Q
  let e : ℤ:=3*(a n ℓ s:ℤ)-c n ℓ s+(D:ℤ)
  let scale:=(ℓ:Padic ℓ)^e*kappa n ℓ s
  let centers:=Port.Unified.Proofs.Hermite.generalPoleCenters (p:=ℓ)
  obtain ⟨QB,rB,hrB,hB⟩:=classBase_simple_poles n ℓ hR s D
  let f : PowerSeries (PadicInt ℓ):=(QB.map (Int.castRingHom (PadicInt ℓ)):PowerSeries (PadicInt ℓ))
  let r : Fin ℓ→PadicInt ℓ:=fun m=>⟨(rB m:Padic ℓ),hrB m⟩
  have hf : PowerSeries.IsRestricted 1 f:=polynomial_isRestricted _
  have hbase:=pole_rep_cleared ℓ (rfX^D*classWeight n ℓ s) QB rB hrB hB
  change atZeroPadic ℓ (rfX^D*classWeight n ℓ s)*integralHahnHom ℓ
    (integralPoleDenominator centers:PowerSeries (PadicInt ℓ))=
      integralHahnHom ℓ (integralPoleNumerator centers f r) at hbase
  have hG : atLocal (pairRF n ℓ P Q) ℓ s*integralHahnHom ℓ
      (integralPoleDenominator centers:PowerSeries (PadicInt ℓ))=
      HahnSeries.C scale*integralHahnHom ℓ (integralPoleNumerator centers
        (integralPoleMulRegular centers (germScaled ℓ Ψ) f r)
        (integralPoleMulResidue centers (germScaled ℓ Ψ) r)):=by
    rw [integralPoleNumerator_mul centers _ f (germScaled_restricted ℓ Ψ),
      (integralHahnHom ℓ).map_mul (germScaled ℓ Ψ) (integralPoleNumerator centers f r),←hbase,
      hfact,germSeries_integralHahn]
    change _=HahnSeries.C scale*_
    dsimp only [scale,e,D]
    ring
  have hκ : kappa n ℓ s≠0:=by
    intro he
    have hh:=kappa_unit n ℓ s
    simp only [Unit,he,norm_zero] at hh
    exact zero_ne_one hh
  have hp : (ℓ:Padic ℓ)≠0:=by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hscale : scale≠0:=mul_ne_zero (zpow_ne_zero e hp) hκ
  have hM : 4*n<ℓ*ℓ:=(hR.1).trans_le (Nat.mul_le_mul_left ℓ (Nat.sub_le ℓ 1))
  have hlocal:=localClass_integral_operator z ℓ hz h1 s ξ (4*n) hM
    ((Port.Li2.D n)^3*(crtE n ℓ P*crtE n ℓ Q)) scale hscale
    (integralPoleMulRegular centers (germScaled ℓ Ψ) f r)
    (integralPoleMulRegular_isRestricted centers _ f (germScaled_restricted ℓ Ψ) hf r)
    (integralPoleMulResidue centers (germScaled ℓ Ψ) r) (by rw [←pairRF_fraction];exact hG)
  rw [←pairRF_fraction] at hlocal
  let hu : z^ℓ≠0∧padicValRat ℓ (z^ℓ)=0:=rational_unit_of_norm ℓ (z^ℓ)
    (by change ‖((z^ℓ:ℚ):Padic ℓ)‖=1;rw [Rat.cast_pow,norm_pow,hz,one_pow])
  let hreg:=(parameter_hypotheses z ℓ hz h1).2.2.1
  change localClass z ℓ s ξ (pairRF n ℓ P Q)=(z:Padic ℓ)^(-(s.val:ℤ))*scale*
    ((Port.Unified.Proofs.Hermite.generalPoleU (z^ℓ) hu hreg
      (integralPoleMulRegular centers (germScaled ℓ Ψ) f r)
      (integralPoleMulResidue centers (germScaled ℓ Ψ) r)).eval₂ _ _-
      (s.val:Padic ℓ)/(ℓ:Padic ℓ)*(Port.Unified.Proofs.Hermite.generalPoleV (z^ℓ) hu hreg
        (integralPoleMulRegular centers (germScaled ℓ Ψ) f r)
        (integralPoleMulResidue centers (germScaled ℓ Ψ) r)).eval₂ _ _) at hlocal
  rw [hlocal]
  by_cases hs : s.val=0
  · simp only [hs,Nat.cast_zero,zero_div,zero_mul,sub_zero,ite_true,chi]
    rw [class_zero_series z n ℓ hu hreg (parameter_hypotheses z ℓ hz h1).2.2.2 hR s ξ D Ψ f hf r hbase y hy]
    have he : nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q=e:=by
      simp only [nu,hs,ite_true,e,D]
      push_cast
      ring
    simp only [hs] at he
    rw [he]
    dsimp only [scale,D]
    ring
  · rw [class_nonzero_series z n ℓ hu hreg (parameter_hypotheses z ℓ hz h1).2.2.2 hR s hs ξ D Ψ f hf r hbase y hy]
    simp only [if_neg hs,Nat.add_zero]
    have he : nu n ℓ s+(d n ℓ s P:ℤ)+d n ℓ s Q=e-1:=by
      simp only [nu,if_neg hs,e,D]
      push_cast
      ring
    rw [he,_root_.zpow_sub₀ hp,zpow_one]
    dsimp only [scale,D]
    ring

private theorem liNeg_frobenius (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ)) (j : ℕ) :
    Port.Li2.VG ℓ ((liNeg j (z^ℓ):ℚ)-liNeg j z) 1 := by
  have hu:=rational_unit_of_norm ℓ z hz
  have hv:=rational_unit_of_norm ℓ (1-z) h1
  have hp:=Port.Unified.Proofs.Arithmetic.one_sub_power_unit_of_hunit z ⟨hu,hv⟩
  have hz0 : Port.Li2.VG ℓ z 0:=Or.inr (by rw [hu.2];norm_num)
  have hf:=Port.Unified.Proofs.Arithmetic.rational_fermat z hz0
  have hi:=Port.Li2.rational_unit_inverse_VG (1-z) hv.1 hv.2
  have hip:=Port.Li2.rational_unit_inverse_VG (1-z^ℓ) hp.1 hp.2
  have hd : Port.Li2.VG ℓ ((1-z^ℓ)-(1-z)) 1:=by
    convert hf.neg using 1 <;> ring
  have hid:=Port.Li2.VG.inv_congr hp.1 hv.1 hip hi hd
  have ht : Port.Li2.VG ℓ (z^ℓ/(1-z^ℓ)-z/(1-z)) 1:=by
    simpa only [div_eq_mul_inv] using Port.Li2.VG.mul_congr hip hz0 hf hid
  have htz : Port.Li2.VG ℓ (z/(1-z)) 0:=by
    simpa only [div_eq_mul_inv,zero_add] using hz0.mul hi
  have htp:=(parameter_hypotheses z ℓ hz h1).2.2.1
  have hw : z≠1:=by intro he;apply hv.1;simp [he]
  rw [liNeg_eq_parameterMoment (z^ℓ) (parameter_hypotheses z ℓ hz h1).2.2.2,
    liNeg_eq_parameterMoment z hw]
  exact Port.Li2.parameterMoment_congr ℓ (z^ℓ) z 1 htp htz ht j


private theorem omega_factor (z : ℚ) (hz : z≠0) (m : ℕ) :
    omega z m=z^(-(m:ℤ))*tauK z m := by
  unfold omega tauK
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [show (b:ℤ)-m=-(m:ℤ)+(b:ℤ) by omega,zpow_add₀ hz]
  simp only [zpow_natCast]
  ring



private theorem omega_frobenius (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (m : ℕ) (hm : m<ℓ) :
    Port.Li2.VG ℓ (omega (z^ℓ) m-omega z m) 1 := by
  have hu:=rational_unit_of_norm ℓ z hz
  have hup:=rational_unit_of_norm ℓ (z^ℓ)
    (by change ‖((z^ℓ:ℚ):Padic ℓ)‖=1;rw [Rat.cast_pow,norm_pow,hz,one_pow])
  have hz0 : Port.Li2.VG ℓ z 0:=Or.inr (by rw [hu.2];norm_num)
  have hzp0 : Port.Li2.VG ℓ (z^ℓ) 0:=by simpa using hz0.pow ℓ
  have hf:=Port.Unified.Proofs.Arithmetic.rational_fermat z hz0
  have hi:=Port.Li2.rational_unit_inverse_VG z hu.1 hu.2
  have hip:=Port.Li2.rational_unit_inverse_VG (z^ℓ) hup.1 hup.2
  have hid:=Port.Li2.VG.inv_congr hup.1 hu.1 hip hi hf
  have hpow:=Port.Li2.VG.pow_congr hip hi hid m
  have htau : Port.Li2.VG ℓ (Port.Li2.parameterTau (z^ℓ) m-Port.Li2.parameterTau z m) 1:=by
    unfold Port.Li2.parameterTau
    rw [←Finset.sum_sub_distrib]
    apply Port.Li2.VG.sum
    intro b hb
    have hbi:=Finset.mem_Icc.mp hb
    have hv : padicValRat ℓ (b:ℚ)=0:=by
      rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd
        (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))]
      rfl
    have hunit:=Port.Li2.rational_unit_inverse_VG (p:=ℓ) (b:ℚ)
      (by exact_mod_cast (by omega : b≠0)) hv
    have hh:=(Port.Li2.VG.pow_congr hzp0 hz0 hf b).mul (hunit.pow 2)
    convert hh using 1 <;> norm_num <;> ring
  have hh:=Port.Li2.VG.mul_congr (Port.Li2.parameterTau_VG (z^ℓ) hzp0 m hm)
    (by simpa using hi.pow m) hpow htau
  rw [omega_factor (z^ℓ) hup.1,omega_factor z hu.1]
  simpa only [_root_.zpow_neg,zpow_natCast,inv_pow,Port.Li2.parameterTau,tauK] using hh

private theorem intg_rat_VG (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ)
    (hq : Intg ℓ (q:Padic ℓ)) : Port.Li2.VG ℓ q 0 := by
  apply (Port.Li2.VG_iff_padic_norm_le q 0).mpr
  simpa only [Intg,Rat.cast_zero,neg_zero,Real.rpow_zero] using hq

private theorem regularV_fraction_frobenius (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (P : ℤ[X]) (S : Finset ℕ) (hS : ∀m∈S,m<ℓ) :
    Port.Li2.VG ℓ ((regularV (z^ℓ) (rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S)):ℚ)-
      regularV z (rfPoly (P.map (Int.castRingHom ℚ))/rfPoly (poleProd S))) 1 := by
  classical
  have hu:=rational_unit_of_norm ℓ z hz
  rw [regularV_fraction _ _ _ (pow_ne_zero ℓ hu.1),regularV_fraction _ _ _ hu.1,add_sub_add_comm]
  apply Port.Li2.VG.add
  · rw [←Finset.sum_sub_distrib]
    apply Port.Li2.VG.sum
    intro m hm
    rw [←mul_sub]
    have hc:=intg_rat_VG ℓ _ (integer_poleCoeff_integral ℓ P S hS m hm)
    simpa only [zero_add] using hc.mul (omega_frobenius z ℓ hz m (hS m hm))
  · rw [←Finset.sum_sub_distrib]
    apply Port.Li2.VG.sum
    intro j hj
    rw [←mul_sub]
    have hc:=intg_rat_VG ℓ _ (integer_quotient_coeff_integral ℓ P S j)
    have hm:=(Port.Li2.VG.natCast (p:=ℓ) j).mul hc
    simpa only [zero_add] using hm.mul (liNeg_frobenius z ℓ hz h1 (j-1))

private def weightNumInt (A : TypeKey) : ℤ[X]:=
  match A.kind with
  | .V=>∏ j∈Finset.range A.a,(X+C (j:ℤ))^2
  | .U=>X*∏ j∈Finset.Icc 1 A.a,(X+C (j:ℤ))^2

private theorem weightNumInt_map (A : TypeKey) :
    (weightNumInt A).map (Int.castRingHom ℚ)=weightNum A := by
  cases hk : A.kind <;>
    simp only [weightNumInt,weightNum,hk,Polynomial.map_prod,Polynomial.map_pow,
      Polynomial.map_mul,Polynomial.map_add,Polynomial.map_X,Polynomial.map_C,
      Int.coe_castRingHom,Int.cast_natCast]

private theorem weight_fraction (A : TypeKey) (e : ℕ) :
    rfX^e*weight A=rfPoly (((X:ℤ[X])^e*weightNumInt A).map (Int.castRingHom ℚ))/
      rfPoly (poleProd (poleSet A)) := by
  rw [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,weightNumInt_map]
  simp only [rfX,weight,weightDen,poleProd,rfPoly,map_mul,map_pow]
  ring


private theorem regularV_weight_frobenius (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (A : TypeKey) (hc : A.c<ℓ) (e : ℕ) :
    Vge ℓ (((regularV (z^ℓ) (rfX^e*weight A):ℚ):Padic ℓ)-
      ((regularV z (rfX^e*weight A):ℚ):Padic ℓ)) 1 := by
  have hS : ∀m∈poleSet A,m<ℓ:=by
    intro m hm
    cases hk : A.kind <;> simp only [poleSet,hk,Finset.mem_Ico,Finset.mem_Ioc] at hm <;> omega
  have hh:=regularV_fraction_frobenius z ℓ hz h1 ((X:ℤ[X])^e*weightNumInt A) (poleSet A) hS
  rw [←weight_fraction] at hh
  have hn:=(Port.Li2.VG_iff_padic_norm_le (regularV (z^ℓ) (rfX^e*weight A)-regularV z (rfX^e*weight A)) 1).mp hh
  simpa only [Vge,Int.cast_one,Rat.cast_one,Rat.cast_sub] using hn

private theorem liNeg_ratCast (j : ℕ) (w : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] :
    ((liNeg j w:ℚ):Padic ℓ)=liNeg j (w:Padic ℓ) := by
  unfold liNeg
  split_ifs <;> push_cast <;> rfl

private theorem tauK_ratCast (m : ℕ) (w : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] :
    ((tauK w m:ℚ):Padic ℓ)=tauK (w:Padic ℓ) m := by
  unfold tauK
  push_cast
  rfl

private theorem regularV_ratCast (w : ℚ) (ℓ : ℕ) [Fact ℓ.Prime] (F : RatFunc ℚ) :
    ((regularV w F:ℚ):Padic ℓ)=regularV (w:Padic ℓ) F := by
  unfold regularV
  simp only [Algebra.algebraMap_self_apply,eq_ratCast,Rat.cast_add,
    Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,Rat.cast_zpow]
  simp_rw [tauK_ratCast,liNeg_ratCast]
  simp only [Rat.cast_id]


private theorem localV_integral_bound (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (A : TypeKey) (hc : A.c<ℓ) (e : ℕ) (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    Intg ℓ (localV z ℓ ξ (rfX^e*weight A)) ∧
      Vge ℓ (localV z ℓ ξ (rfX^e*weight A)-localV z ℓ 0 (rfX^e*weight A)) 1 := by
  obtain ⟨a,b,ha,hb⟩:=localV_integral_affine z ℓ hz h1 A hc e
  have hp : (0:ℝ)<ℓ:=by exact_mod_cast (Fact.out : ℓ.Prime).pos
  have hξ' : ‖ξ‖≤(ℓ:ℝ):=by
    simpa only [Vge,Int.cast_neg,Int.cast_one,neg_neg,Real.rpow_one] using hξ
  have hscale : ‖(ℓ:Padic ℓ)^2*ξ‖≤(ℓ:ℝ)⁻¹:=by
    rw [norm_mul,norm_pow,Padic.norm_p]
    calc
      (ℓ:ℝ)⁻¹^2*‖ξ‖≤(ℓ:ℝ)⁻¹^2*ℓ:=mul_le_mul_of_nonneg_left hξ' (sq_nonneg _)
      _=(ℓ:ℝ)⁻¹:=by field_simp <;> ring
  have hlin : ‖(b:Padic ℓ)*(ℓ:Padic ℓ)^2*ξ‖≤(ℓ:ℝ)⁻¹:=by
    rw [mul_assoc,norm_mul]
    simpa only [one_mul] using! mul_le_mul (PadicInt.norm_le_one b) hscale (norm_nonneg _) (by positivity)
  have hinv : (ℓ:ℝ)⁻¹≤1:=(inv_le_one₀ hp).mpr (by exact_mod_cast (Fact.out : ℓ.Prime).one_le)
  constructor
  · rw [hb ξ]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (PadicInt.norm_le_one a) (hlin.trans hinv))
  · rw [hb ξ,hb 0]
    simp only [mul_zero,add_zero,add_sub_cancel_left]
    simpa only [Vge,Int.cast_one,Real.rpow_neg_one] using hlin


private theorem Vge_add_same (ℓ : ℕ) [Fact ℓ.Prime] (x y : Padic ℓ) (e : ℤ)
    (hx : Vge ℓ x e) (hy : Vge ℓ y e) : Vge ℓ (x+y) e :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

private theorem localV_L_congr (z : ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (A : TypeKey) (hc : A.c<ℓ) (e : ℕ) (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    Vge ℓ (localV z ℓ ξ (rfX^e*weight A)-(L A z (X^e):Padic ℓ)) 1 := by
  obtain ⟨a,b,ha,hb⟩:=localV_integral_affine z ℓ hz h1 A hc e
  have hzero : localV z ℓ 0 (rfX^e*weight A)=
      ((regularV (z^ℓ) (rfX^e*weight A):ℚ):Padic ℓ):=by
    calc
      _=(a:Padic ℓ):=by rw [hb 0];ring
      _=_:=by simpa only [←Rat.cast_pow,←regularV_ratCast] using ha
  have hL : (L A z (X^e):Padic ℓ)=((regularV z (rfX^e*weight A):ℚ):Padic ℓ):=by
    simp only [L,rfPoly,rfX,map_pow]
  rw [hL]
  have he : localV z ℓ ξ (rfX^e*weight A)-((regularV z (rfX^e*weight A):ℚ):Padic ℓ)=
      (localV z ℓ ξ (rfX^e*weight A)-localV z ℓ 0 (rfX^e*weight A))+
        (((regularV (z^ℓ) (rfX^e*weight A):ℚ):Padic ℓ)-((regularV z (rfX^e*weight A):ℚ):Padic ℓ)):=by
    rw [hzero]
    ring
  rw [he]
  exact Vge_add_same ℓ _ _ 1 (localV_integral_bound z ℓ hz h1 A hc e ξ hξ).2
    (regularV_weight_frobenius z ℓ hz h1 A hc e)

private theorem classRF_eq (n ℓ : ℕ) (s : Fin ℓ) (d j : ℕ) :
    rfX^(d+(if s.val=0 then 1 else 0)+j)*classWeight n ℓ s=
      rfX^(d+j)*weight (classKey n ℓ s) := by
  have hx : (rfX:RatFunc ℚ)≠0:=RatFunc.algebraMap_ne_zero (by simp)
  by_cases hs : s.val=0
  · simp only [classWeight,if_pos hs]
    rw [show d+1+j=d+j+1 by omega,pow_succ]
    field_simp
  · simp only [classWeight,if_neg hs,Nat.add_zero]

private theorem local_term_bound (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (d : ℕ) (Ψ : Germ ℓ)
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) (j : ℕ) :
    ‖(ℓ:Padic ℓ)^j*(chi ℓ s Ψ j:Padic ℓ)*
      localV z ℓ ξ (rfX^(d+(if s.val=0 then 1 else 0)+j)*classWeight n ℓ s)‖≤‖(ℓ:Padic ℓ)‖^j := by
  have hc : (classKey n ℓ s).c<ℓ:=by
    change c n ℓ s<ℓ
    have h:=(class_counts n ℓ hR).1 s
    have hp:=(Fact.out : ℓ.Prime).pos
    omega
  have hi:=(localV_integral_bound z ℓ hz h1 (classKey n ℓ s) hc (d+j) ξ hξ).1
  rw [classRF_eq,norm_mul,norm_mul,norm_pow]
  calc
    _≤(‖(ℓ:Padic ℓ)‖^j*1)*1:=mul_le_mul
      (mul_le_mul_of_nonneg_left (PadicInt.norm_le_one (chi ℓ s Ψ j)) (pow_nonneg (norm_nonneg _) j))
      hi (norm_nonneg _) (by positivity)
    _=‖(ℓ:Padic ℓ)‖^j:=by ring

private theorem local_terms_summable (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (d : ℕ) (Ψ : Germ ℓ)
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    Summable (fun j : ℕ=>(ℓ:Padic ℓ)^j*(chi ℓ s Ψ j:Padic ℓ)*
      localV z ℓ ξ (rfX^(d+(if s.val=0 then 1 else 0)+j)*classWeight n ℓ s)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop,tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun j=>norm_nonneg _) (local_term_bound z n ℓ hz h1 hR s d Ψ ξ hξ)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (ℓ:Padic ℓ)) Padic.norm_p_lt_one)

private def expansionTerm (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (s : Fin ℓ) (d : ℕ) (Ψ : Germ ℓ) (ξ : Padic ℓ) (j : ℕ) : Padic ℓ:=
  (ℓ:Padic ℓ)^j*(chi ℓ s Ψ j:Padic ℓ)*
    localV z ℓ ξ (rfX^(d+(if s.val=0 then 1 else 0)+j)*classWeight n ℓ s)

private theorem expansion_sum_integral (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (d : ℕ) (Ψ : Germ ℓ)
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    Intg ℓ (∑' j,expansionTerm z n ℓ s d Ψ ξ j) := by
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro j
  exact (local_term_bound z n ℓ hz h1 hR s d Ψ ξ hξ j).trans
    (pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le)

private theorem expansion_sum_tail (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (d : ℕ) (Ψ : Germ ℓ)
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    Vge ℓ ((∑' j,expansionTerm z n ℓ s d Ψ ξ j)-expansionTerm z n ℓ s d Ψ ξ 0) 1 := by
  have hs : Summable (expansionTerm z n ℓ s d Ψ ξ):=local_terms_summable z n ℓ hz h1 hR s d Ψ ξ hξ
  have he:=hs.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at he
  change expansionTerm z n ℓ s d Ψ ξ 0+∑' j,expansionTerm z n ℓ s d Ψ ξ (j+1)=
    ∑' j,expansionTerm z n ℓ s d Ψ ξ j at he
  rw [←he,add_sub_cancel_left]
  have hb : ‖∑' j,expansionTerm z n ℓ s d Ψ ξ (j+1)‖≤‖(ℓ:Padic ℓ)‖:=by
    apply IsUltrametricDist.norm_tsum_le_of_forall_le
    intro j
    calc
      _≤‖(ℓ:Padic ℓ)‖^(j+1):=local_term_bound z n ℓ hz h1 hR s d Ψ ξ hξ (j+1)
      _≤‖(ℓ:Padic ℓ)‖:=by
        rw [pow_succ]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le : ‖(ℓ:Padic ℓ)‖^j≤1) (norm_nonneg _)
  simpa only [Vge,Int.cast_one,Real.rpow_neg_one,Padic.norm_p] using hb

private theorem expansion_sum_xi_difference (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (d : ℕ) (Ψ : Germ ℓ)
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    Vge ℓ ((∑' j,expansionTerm z n ℓ s d Ψ ξ j)-
      ∑' j,expansionTerm z n ℓ s d Ψ 0 j) 1 := by
  have hξ0 : Vge ℓ (0:Padic ℓ) (-1):=by unfold Vge;rw [norm_zero];positivity
  have hsξ : Summable (expansionTerm z n ℓ s d Ψ ξ):=local_terms_summable z n ℓ hz h1 hR s d Ψ ξ hξ
  have hs0 : Summable (expansionTerm z n ℓ s d Ψ 0):=local_terms_summable z n ℓ hz h1 hR s d Ψ 0 hξ0
  rw [←hsξ.tsum_sub hs0]
  have hc : (classKey n ℓ s).c<ℓ:=by
    change c n ℓ s<ℓ
    have h:=(class_counts n ℓ hR).1 s
    have hp:=(Fact.out : ℓ.Prime).pos
    omega
  have hb : ‖∑' j,(expansionTerm z n ℓ s d Ψ ξ j - expansionTerm z n ℓ s d Ψ 0 j)‖≤‖(ℓ:Padic ℓ)‖:=by
    apply IsUltrametricDist.norm_tsum_le_of_forall_le
    intro j
    have hdiff:= (localV_integral_bound z ℓ hz h1 (classKey n ℓ s) hc (d+j) ξ hξ).2
    have hnorm : ‖localV z ℓ ξ (rfX^(d+j)*weight (classKey n ℓ s))-
        localV z ℓ 0 (rfX^(d+j)*weight (classKey n ℓ s))‖≤‖(ℓ:Padic ℓ)‖:=by
      simpa only [Vge,Int.cast_one,Real.rpow_neg_one,Padic.norm_p] using hdiff
    unfold expansionTerm
    rw [classRF_eq,←mul_sub,norm_mul,norm_mul,norm_pow]
    calc
      _≤(‖(ℓ:Padic ℓ)‖^j*1)*‖(ℓ:Padic ℓ)‖:=by
        simpa only [PadicInt.norm_def] using! mul_le_mul
          (mul_le_mul_of_nonneg_left (PadicInt.norm_le_one (chi ℓ s Ψ j)) (pow_nonneg (norm_nonneg _) j))
          hnorm (norm_nonneg _) (by positivity)
      _≤‖(ℓ:Padic ℓ)‖:=by
        rw [mul_one]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le : ‖(ℓ:Padic ℓ)‖^j≤1) (norm_nonneg _)
  simpa only [Vge,Int.cast_one,Real.rpow_neg_one,Padic.norm_p] using hb


private theorem Vge_mul_levels (ℓ : ℕ) [Fact ℓ.Prime] (x y : Padic ℓ) (e f : ℤ)
    (hx : Vge ℓ x e) (hy : Vge ℓ y f) : Vge ℓ (x*y) (e+f) := by
  have hp : (0:ℝ)<ℓ:=by exact_mod_cast (Fact.out : ℓ.Prime).pos
  unfold Vge at hx hy ⊢
  rw [norm_mul]
  calc
    _≤(ℓ:ℝ)^(-(e:ℝ))*(ℓ:ℝ)^(-(f:ℝ)):=mul_le_mul hx hy (norm_nonneg _) (by positivity)
    _=_:=by rw [←Real.rpow_add hp];congr 1;push_cast;ring

private theorem Vge_prime_power (ℓ : ℕ) [Fact ℓ.Prime] (e : ℤ) :
    Vge ℓ ((ℓ:Padic ℓ)^e) e := by
  unfold Vge
  rw [←Int.cast_neg,Real.rpow_intCast,Padic.norm_p_zpow]

private theorem Vge_unit_scalar (ℓ : ℕ) [Fact ℓ.Prime] (u x : Padic ℓ)
    (hu : Unit ℓ u) (e : ℤ) (hx : Vge ℓ x e) : Vge ℓ (u*x) e := by
  unfold Vge
  rw [norm_mul,hu,one_mul]
  exact hx

private theorem Vge_scaled (ℓ : ℕ) [Fact ℓ.Prime] (u x : Padic ℓ)
    (hu : Unit ℓ u) (e f : ℤ) (hx : Vge ℓ x f) :
    Vge ℓ (u*(ℓ:Padic ℓ)^e*x) (e+f) := by
  rw [mul_assoc]
  exact Vge_unit_scalar ℓ u _ hu (e+f) (Vge_mul_levels ℓ _ _ e f (Vge_prime_power ℓ e) hx)

private theorem scaled_coordinate_integral (ℓ : ℕ) [Fact ℓ.Prime]
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) : Intg ℓ ((ℓ:Padic ℓ)^2*ξ) := by
  have hp : (0:ℝ)<ℓ:=by exact_mod_cast (Fact.out : ℓ.Prime).pos
  have hξ' : ‖ξ‖≤(ℓ:ℝ):=by
    simpa only [Vge,Int.cast_neg,Int.cast_one,neg_neg,Real.rpow_one] using hξ
  unfold Intg
  rw [norm_mul,norm_pow,Padic.norm_p]
  calc
    (ℓ:ℝ)⁻¹^2*‖ξ‖≤(ℓ:ℝ)⁻¹^2*ℓ:=mul_le_mul_of_nonneg_left hξ' (sq_nonneg _)
    _=(ℓ:ℝ)⁻¹:=by field_simp <;> ring
    _≤1:=(inv_le_one₀ hp).mpr (by exact_mod_cast (Fact.out : ℓ.Prime).one_le)


private theorem expansion_sum_leading (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (d : ℕ) (Ψ : Germ ℓ)
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    Vge ℓ ((∑'j,expansionTerm z n ℓ s d Ψ ξ j)-
      (chi ℓ s Ψ 0:Padic ℓ)*(L (classKey n ℓ s) z (X^d):Padic ℓ)) 1 := by
  have hc : (classKey n ℓ s).c<ℓ:=by
    change c n ℓ s<ℓ
    have hh:=(class_counts n ℓ hR).1 s
    have hp:=(Fact.out : ℓ.Prime).pos
    omega
  have ht : expansionTerm z n ℓ s d Ψ ξ 0=
      (chi ℓ s Ψ 0:Padic ℓ)*localV z ℓ ξ (rfX^d*weight (classKey n ℓ s)):=by
    unfold expansionTerm
    rw [classRF_eq]
    simp only [pow_zero,one_mul,Nat.add_zero]
  have he : (∑'j,expansionTerm z n ℓ s d Ψ ξ j)-
      (chi ℓ s Ψ 0:Padic ℓ)*(L (classKey n ℓ s) z (X^d):Padic ℓ)=
    ((∑'j,expansionTerm z n ℓ s d Ψ ξ j)-expansionTerm z n ℓ s d Ψ ξ 0)+
      (chi ℓ s Ψ 0:Padic ℓ)*(localV z ℓ ξ (rfX^d*weight (classKey n ℓ s))-
        (L (classKey n ℓ s) z (X^d):Padic ℓ)):=by rw [ht];ring
  rw [he]
  apply Vge_add_same ℓ _ _ 1 (expansion_sum_tail z n ℓ hz h1 hR s d Ψ ξ hξ)
  have hχ : Vge ℓ (chi ℓ s Ψ 0:Padic ℓ) 0:=by
    simpa only [Vge,Int.cast_zero,neg_zero,Real.rpow_zero,PadicInt.norm_def] using PadicInt.norm_le_one (chi ℓ s Ψ 0)
  simpa only [zero_add] using Vge_mul_levels ℓ _ _ 0 1 hχ
    (localV_L_congr z ℓ hz h1 (classKey n ℓ s) hc d ξ hξ)

private theorem localClass_factor_leading (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (P Q : Ix n ℓ) (Ψ : Germ ℓ)
    (hfact : atLocal (pairRF n ℓ P Q) ℓ s=
      HahnSeries.C ((ℓ:Padic ℓ)^((3*(a n ℓ s:ℤ)-c n ℓ s)+((d n ℓ s P+d n ℓ s Q:ℕ):ℤ))*kappa n ℓ s)*
        atZeroPadic ℓ (rfX^(d n ℓ s P+d n ℓ s Q)*classWeight n ℓ s)*germSeries ℓ Ψ)
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    let D:=d n ℓ s P+d n ℓ s Q
    let e : ℤ:=nu n ℓ s+(D:ℤ)
    Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q)-
      (z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s*(ℓ:Padic ℓ)^e*
        ((chi ℓ s Ψ 0:Padic ℓ)*(L (classKey n ℓ s) z (X^D):Padic ℓ))) (e+1) := by
  intro D e
  let y : PadicInt ℓ:=⟨(ℓ:Padic ℓ)^2*ξ,scaled_coordinate_integral ℓ ξ hξ⟩
  have hs:=localClass_factor_series z n ℓ hz h1 hR s P Q Ψ hfact ξ y rfl
  have hseries : localClass z ℓ s ξ (pairRF n ℓ P Q)=
      (z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s*(ℓ:Padic ℓ)^e*
        ∑'j,expansionTerm z n ℓ s D Ψ ξ j:=by
    simpa only [D,e,expansionTerm,Nat.cast_add,add_assoc] using hs
  have hu : Unit ℓ ((z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s):=by
    change ‖(z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s‖=1
    rw [norm_mul,norm_zpow,hz,kappa_unit n ℓ s,one_zpow,one_mul]
  have hv:=Vge_scaled ℓ ((z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s)
    ((∑'j,expansionTerm z n ℓ s D Ψ ξ j)-
      (chi ℓ s Ψ 0:Padic ℓ)*(L (classKey n ℓ s) z (X^D):Padic ℓ)) hu e 1
        (expansion_sum_leading z n ℓ hz h1 hR s D Ψ ξ hξ)
  rw [hseries]
  convert hv using 1 <;> ring
def mC (n ℓ : ℕ) : ℕ := 2*(n/ℓ)+k n ℓ-2
def m0 (n ℓ : ℕ) : ℕ := 2*(n/ℓ)+k n ℓ
def keyC (n ℓ : ℕ) : TypeKey := ⟨.V,n/ℓ+1,4*(n/ℓ)+k n ℓ,mC n ℓ⟩
def keyCplus (n ℓ : ℕ) : TypeKey := ⟨.V,n/ℓ+1,4*(n/ℓ)+k n ℓ,mC n ℓ+1⟩
def keyU (n ℓ : ℕ) : TypeKey := ⟨.U,n/ℓ,4*(n/ℓ)+k n ℓ,m0 n ℓ⟩
def keyUminus (n ℓ : ℕ) : TypeKey := ⟨.U,n/ℓ,4*(n/ℓ)+k n ℓ,m0 n ℓ-1⟩
def sameLeading (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ)
    (ξ : Padic ℓ) : Prop :=
  ∀ P Q : Ix n ℓ, P.1=s → Q.1=s →
    Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q) -
      (uQ z n ℓ s:Padic ℓ)*(ℓ:Padic ℓ)^(nu n ℓ s+P.2.val+Q.2.val)*
        (L (classKey n ℓ s) z (X^(P.2.val+Q.2.val)):Padic ℓ))
      (nu n ℓ s+P.2.val+Q.2.val+1)
def tiedLeading (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime] (s : Fin ℓ)
    (ξ : Padic ℓ) : Prop :=
  s.val∈Cset n ℓ →
    (∀ P Q : Ix n ℓ, P.1=s → Q.1.val=0 → Q.2.val+1=m0 n ℓ →
      Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q) -
        (uQ z n ℓ s:Padic ℓ)/(-(s:Padic ℓ))*
          (ℓ:Padic ℓ)^(nu n ℓ s+P.2.val+mC n ℓ)*
          (L (keyC n ℓ) z (X^(P.2.val+mC n ℓ)):Padic ℓ))
        (nu n ℓ s+P.2.val+mC n ℓ+1)) ∧
    (∀ P Q : Ix n ℓ, P.1.val=0 → Q.1.val=0 →
      P.2.val+1=m0 n ℓ → Q.2.val+1=m0 n ℓ →
      Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q) -
        (uQ z n ℓ s:Padic ℓ)/(s:Padic ℓ)^2*
          (ℓ:Padic ℓ)^(nu n ℓ s+2*mC n ℓ)*
          (L (keyC n ℓ) z (X^(2*mC n ℓ)):Padic ℓ))
        (nu n ℓ s+2*mC n ℓ+1))


private theorem same_class_leading (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    sameLeading z n ℓ s ξ := by
  intro P Q hP hQ
  obtain ⟨Ψ,hunit,hκ,hfact,hzero⟩:=local_factorization n ℓ hR s P Q
  have hfact' : atLocal (pairRF n ℓ P Q) ℓ s=
      HahnSeries.C ((ℓ:Padic ℓ)^((3*(a n ℓ s:ℤ)-c n ℓ s)+((d n ℓ s P+d n ℓ s Q:ℕ):ℤ))*kappa n ℓ s)*
        atZeroPadic ℓ (rfX^(d n ℓ s P+d n ℓ s Q)*classWeight n ℓ s)*germSeries ℓ Ψ:=by
    simpa only [pairRF,HahnSeries.C_apply,Nat.cast_add,add_assoc] using hfact
  have hv:=localClass_factor_leading z n ℓ hz h1 hR s P Q Ψ hfact' ξ hξ
  rw [same_pair_constant n ℓ s P Q hP hQ] at hzero
  have hcoef : (z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s*(chi ℓ s Ψ 0:Padic ℓ)=
      (uQ z n ℓ s:Padic ℓ):=by
    by_cases hs : s.val=0
    · simp only [chi,hs,ite_true,Nat.cast_zero,Int.cast_zero,neg_zero,zpow_zero,one_mul]
      rw [hzero]
      simp only [uQ,hs,ite_true,one_mul,Rat.cast_mul,Rat.cast_pow,kappa]
    · simp only [chi,if_neg hs,ite_true,add_zero,PadicInt.coe_mul,PadicInt.coe_neg,PadicInt.coe_natCast]
      rw [hzero]
      simp only [uQ,if_neg hs,kappa,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_zpow,Rat.cast_natCast]
      ring
  dsimp only at hv
  have hD : d n ℓ s P+d n ℓ s Q=P.2.val+Q.2.val:=by simp only [d,hP,hQ,ite_true]
  rw [hD] at hv
  simp only [Nat.cast_add,←add_assoc] at hv
  have ht : (z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s*
      (ℓ:Padic ℓ)^(nu n ℓ s+P.2.val+Q.2.val)*
        ((chi ℓ s Ψ 0:Padic ℓ)*(L (classKey n ℓ s) z (X^(P.2.val+Q.2.val)):Padic ℓ))=
      (uQ z n ℓ s:Padic ℓ)*(ℓ:Padic ℓ)^(nu n ℓ s+P.2.val+Q.2.val)*
        (L (classKey n ℓ s) z (X^(P.2.val+Q.2.val)):Padic ℓ):=by
    rw [←hcoef]
    ring
  rw [ht] at hv
  exact hv
private theorem class_zero_count (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ) :
    m n ℓ 0=m0 n ℓ := by
  let s : Fin ℓ:=⟨0,(Fact.out : ℓ.Prime).pos⟩
  have h:=(class_counts n ℓ hR).2.2 s
  have ha:=congrArg Prod.fst h
  have hc:=congrArg Prod.snd h
  simp only [s,typeAC,ne_eq,not_true_eq_false,false_and,ite_false,Nat.add_zero] at ha hc
  dsimp only [m,m0]
  rw [ha,hc]
  omega
private theorem class_C_key (n ℓ : ℕ) [Fact ℓ.Prime] (hR : Range n ℓ)
    (s : Fin ℓ) (hs : s.val∈Cset n ℓ) :
    s.val≠0 ∧ m n ℓ s=mC n ℓ ∧ classKey n ℓ s=keyC n ℓ := by
  have hi : r' n ℓ<s.val∧s.val≤r n ℓ:=Finset.mem_Ioc.mp hs
  have hzero : s.val≠0:=by omega
  have hlt : ¬s.val≤r' n ℓ:=by omega
  have h:=(class_counts n ℓ hR).2.2 s
  have ha:=congrArg Prod.fst h
  have hc:=congrArg Prod.snd h
  simp only [typeAC,hzero,ne_eq,not_false_eq_true,true_and,hi.2,hlt,ite_true,ite_false,Nat.add_zero] at ha hc
  have hm : m n ℓ s=mC n ℓ:=by
    unfold m mC
    rw [ha,hc]
    omega
  refine ⟨hzero,hm,?_⟩
  simp only [classKey,if_neg hzero,keyC,ha,hc,hm]

private theorem nonzero_pair_leading_divisor (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (hs : s.val≠0) (P Q : Ix n ℓ) (den : ℚ)
    (hconst : (crtE n ℓ P*crtE n ℓ Q /ₘ (X+C (s:ℚ))^(d n ℓ s P+d n ℓ s Q)).eval (-(s:ℚ))=
      (crtPi n ℓ s).eval (-(s:ℚ))^2/den)
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    let D:=d n ℓ s P+d n ℓ s Q
    let e : ℤ:=nu n ℓ s+(D:ℤ)
    Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q)-
      (uQ z n ℓ s:Padic ℓ)/(den:Padic ℓ)*(ℓ:Padic ℓ)^e*
        (L (classKey n ℓ s) z (X^D):Padic ℓ)) (e+1) := by
  intro D e
  obtain ⟨Ψ,hunit,hκ,hfact,hzero⟩:=local_factorization n ℓ hR s P Q
  have hfact' : atLocal (pairRF n ℓ P Q) ℓ s=
      HahnSeries.C ((ℓ:Padic ℓ)^((3*(a n ℓ s:ℤ)-c n ℓ s)+((d n ℓ s P+d n ℓ s Q:ℕ):ℤ))*kappa n ℓ s)*
        atZeroPadic ℓ (rfX^(d n ℓ s P+d n ℓ s Q)*classWeight n ℓ s)*germSeries ℓ Ψ:=by
    simpa only [pairRF,HahnSeries.C_apply,Nat.cast_add,add_assoc] using hfact
  have hv:=localClass_factor_leading z n ℓ hz h1 hR s P Q Ψ hfact' ξ hξ
  rw [hconst] at hzero
  have hcoef : (z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s*(chi ℓ s Ψ 0:Padic ℓ)=
      (uQ z n ℓ s:Padic ℓ)/(den:Padic ℓ):=by
    simp only [chi,if_neg hs,ite_true,add_zero,PadicInt.coe_mul,PadicInt.coe_neg,PadicInt.coe_natCast]
    rw [hzero]
    simp only [uQ,if_neg hs,kappa,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_zpow,Rat.cast_natCast,Rat.cast_div]
    ring
  dsimp only at hv
  change Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q)-
    (z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s*(ℓ:Padic ℓ)^e*
      ((chi ℓ s Ψ 0:Padic ℓ)*(L (classKey n ℓ s) z (X^D):Padic ℓ))) (e+1) at hv
  have ht : (z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s*(ℓ:Padic ℓ)^e*
      ((chi ℓ s Ψ 0:Padic ℓ)*(L (classKey n ℓ s) z (X^D):Padic ℓ))=
      (uQ z n ℓ s:Padic ℓ)/(den:Padic ℓ)*(ℓ:Padic ℓ)^e*
        (L (classKey n ℓ s) z (X^D):Padic ℓ):=by rw [←hcoef];ring
  rw [ht] at hv
  exact hv
private theorem tied_class_leading (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    tiedLeading z n ℓ s ξ := by
  intro hsC
  obtain ⟨hs,hmC,hkey⟩:=class_C_key n ℓ hR s hsC
  have hm0:=class_zero_count n ℓ hR
  constructor
  · intro P Q hP hQ hlast
    have hsQ : s≠Q.1:=by intro he;apply hs;rw [he];exact hQ
    have hlast' : Q.2.val+1=m n ℓ Q.1:=by simpa only [hQ] using hlast.trans hm0.symm
    have hc:=mixed_last_constant n ℓ s P Q hP hsQ hlast'
    have hd : ((Q.1:ℚ)-(s:ℚ))=-(s:ℚ):=by simp only [show (Q.1:ℚ)=(0:ℚ) by exact_mod_cast hQ,zero_sub]
    rw [hd] at hc
    have hv:=nonzero_pair_leading_divisor z n ℓ hz h1 hR s hs P Q (-(s:ℚ)) hc ξ hξ
    have hD : d n ℓ s P+d n ℓ s Q=P.2.val+mC n ℓ:=by
      simp only [d,hP,ite_true,if_neg hsQ,hmC]
    dsimp only at hv
    rw [hD,hkey] at hv
    simpa only [Nat.cast_add,Rat.cast_neg,Rat.cast_natCast,←add_assoc] using hv
  · intro P Q hP hQ hlastP hlastQ
    have hsP : s≠P.1:=by intro he;apply hs;rw [he];exact hP
    have hsQ : s≠Q.1:=by intro he;apply hs;rw [he];exact hQ
    have hlastP' : P.2.val+1=m n ℓ P.1:=by simpa only [hP] using hlastP.trans hm0.symm
    have hlastQ' : Q.2.val+1=m n ℓ Q.1:=by simpa only [hQ] using hlastQ.trans hm0.symm
    have hc:=both_last_constant n ℓ s P Q hsP hsQ hlastP' hlastQ'
    have hd : (((P.1:ℚ)-(s:ℚ))*((Q.1:ℚ)-(s:ℚ)))=(s:ℚ)^2:=by
      rw [show (P.1:ℚ)=0 by exact_mod_cast hP,show (Q.1:ℚ)=0 by exact_mod_cast hQ]
      ring
    rw [hd] at hc
    have hv:=nonzero_pair_leading_divisor z n ℓ hz h1 hR s hs P Q ((s:ℚ)^2) hc ξ hξ
    have hD : d n ℓ s P+d n ℓ s Q=2*mC n ℓ:=by
      simp only [d,if_neg hsP,if_neg hsQ,hmC]
      omega
    dsimp only at hv
    rw [hD,hkey] at hv
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast,←add_assoc] using hv
private theorem localClass_factor_bounds (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (P Q : Ix n ℓ) (Ψ : Germ ℓ)
    (hfact : atLocal (pairRF n ℓ P Q) ℓ s=
      HahnSeries.C ((ℓ:Padic ℓ)^((3*(a n ℓ s:ℤ)-c n ℓ s)+((d n ℓ s P+d n ℓ s Q:ℕ):ℤ))*kappa n ℓ s)*
        atZeroPadic ℓ (rfX^(d n ℓ s P+d n ℓ s Q)*classWeight n ℓ s)*germSeries ℓ Ψ)
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
    let D:=d n ℓ s P+d n ℓ s Q
    let e : ℤ:=nu n ℓ s+(D:ℤ)
    Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q)) e ∧
      Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q)-localClass z ℓ s 0 (pairRF n ℓ P Q)) (e+1) := by
  intro D e
  let u:=(z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s
  have hu : Unit ℓ u:=by
    change ‖(z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s‖=1
    rw [norm_mul,norm_zpow,hz,kappa_unit n ℓ s,one_zpow,one_mul]
  have hseries (η : Padic ℓ) (hη : Vge ℓ η (-1)) :
      localClass z ℓ s η (pairRF n ℓ P Q)=
        u*(ℓ:Padic ℓ)^e*∑'j,expansionTerm z n ℓ s D Ψ η j:=by
    let y : PadicInt ℓ:=⟨(ℓ:Padic ℓ)^2*η,scaled_coordinate_integral ℓ η hη⟩
    simpa only [u,e,D,expansionTerm,Nat.cast_add,add_assoc] using
      localClass_factor_series z n ℓ hz h1 hR s P Q Ψ hfact η y rfl
  have hzero : Vge ℓ (0:Padic ℓ) (-1):=by unfold Vge;rw [norm_zero];positivity
  constructor
  · rw [hseries ξ hξ]
    have hi : Vge ℓ (∑'j,expansionTerm z n ℓ s D Ψ ξ j) 0:=by
      simpa only [Intg,Vge,Int.cast_zero,neg_zero,Real.rpow_zero] using
        expansion_sum_integral z n ℓ hz h1 hR s D Ψ ξ hξ
    simpa only [add_zero] using Vge_scaled ℓ u _ hu e 0 hi
  · rw [hseries ξ hξ,hseries 0 hzero,←mul_sub]
    exact Vge_scaled ℓ u _ hu e 1 (expansion_sum_xi_difference z n ℓ hz h1 hR s D Ψ ξ hξ)
theorem local_expansion (z : ℚ) (n ℓ : ℕ) [Fact ℓ.Prime]
    (hz : Unit ℓ (z:Padic ℓ)) (h1 : Unit ℓ ((1-z:ℚ):Padic ℓ))
    (hR : Range n ℓ) (s : Fin ℓ) (P Q : Ix n ℓ)
    (ξ : Padic ℓ) (hξ : Vge ℓ ξ (-1)) :
  ∃ Ψ : Germ ℓ,
    IsUnit (Ψ 0) ∧
    atLocal (pairRF n ℓ P Q) ℓ s =
      HahnSeries.single 0 ((ℓ:Padic ℓ)^((3*(a n ℓ s:ℤ)-c n ℓ s)+
        d n ℓ s P+d n ℓ s Q)*kappa n ℓ s)*
      atZeroPadic ℓ (rfX^(d n ℓ s P+d n ℓ s Q)*classWeight n ℓ s)*germSeries ℓ Ψ ∧
    let term := fun j : ℕ => (ℓ:Padic ℓ)^j*(chi ℓ s Ψ j:Padic ℓ)*
      localV z ℓ ξ (rfX^(d n ℓ s P+d n ℓ s Q+(if s.val=0 then 1 else 0)+j)*
        classWeight n ℓ s)
    Summable term ∧
    localClass z ℓ s ξ (pairRF n ℓ P Q) =
      (z:Padic ℓ)^(-(s.val:ℤ))*kappa n ℓ s*
        (ℓ:Padic ℓ)^(nu n ℓ s+d n ℓ s P+d n ℓ s Q)*(∑' j, term j) ∧
    Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q))
      (nu n ℓ s+d n ℓ s P+d n ℓ s Q) ∧
    Vge ℓ (localClass z ℓ s ξ (pairRF n ℓ P Q)-
      localClass z ℓ s 0 (pairRF n ℓ P Q))
      (nu n ℓ s+d n ℓ s P+d n ℓ s Q+1) ∧
    sameLeading z n ℓ s ξ ∧ tiedLeading z n ℓ s ξ := by
  obtain ⟨Ψ,hunit,hκ,hfact,hzero⟩:=local_factorization n ℓ hR s P Q
  have hfact' : atLocal (pairRF n ℓ P Q) ℓ s=
      HahnSeries.C ((ℓ:Padic ℓ)^((3*(a n ℓ s:ℤ)-c n ℓ s)+((d n ℓ s P+d n ℓ s Q:ℕ):ℤ))*kappa n ℓ s)*
        atZeroPadic ℓ (rfX^(d n ℓ s P+d n ℓ s Q)*classWeight n ℓ s)*germSeries ℓ Ψ:=by
    simpa only [pairRF,HahnSeries.C_apply,Nat.cast_add,add_assoc] using hfact
  refine ⟨Ψ,hunit,?_,?_⟩
  · simpa only [pairRF] using hfact
  · dsimp only
    refine ⟨local_terms_summable z n ℓ hz h1 hR s (d n ℓ s P+d n ℓ s Q) Ψ ξ hξ,?_,?_,?_,
      same_class_leading z n ℓ hz h1 hR s ξ hξ,tied_class_leading z n ℓ hz h1 hR s ξ hξ⟩
    · let y : PadicInt ℓ:=⟨(ℓ:Padic ℓ)^2*ξ,scaled_coordinate_integral ℓ ξ hξ⟩
      exact localClass_factor_series z n ℓ hz h1 hR s P Q Ψ hfact' ξ y rfl
    · simpa only [Nat.cast_add,add_assoc] using
        (localClass_factor_bounds z n ℓ hz h1 hR s P Q Ψ hfact' ξ hξ).1
    · simpa only [Nat.cast_add,add_assoc] using
        (localClass_factor_bounds z n ℓ hz h1 hR s P Q Ψ hfact' ξ hξ).2
#print axioms local_factorization
#print axioms local_expansion
end
end CatalanCore.Li2.NV
