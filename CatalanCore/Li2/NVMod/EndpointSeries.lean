module
public import CatalanCore.Li2.NVMod.InfinityMap
public import CatalanCore.Li2.NVMod.LaurentBounds
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

def intPolyRF (P : ℤ[X]) : RatFunc ℚ := rfPoly (P.map (Int.castRingHom ℚ))

theorem atZero_rfPoly (P : ℚ[X]) : atZero (rfPoly P)=polyHahnQ P := by
  rw [atZero_eq_hom]
  simp only [affineRFHahnQ,rfPoly,RatFunc.liftRingHom_algebraMap]
  simp [affinePolyHahnQ]

theorem atOne_rfPoly (P : ℚ[X]) : atOne (rfPoly P)=polyHahnQ (P.comp (1-X)) := by
  rw [atOne_eq_hom]
  simp only [affineRFHahnQ,rfPoly,RatFunc.liftRingHom_algebraMap]
  change polyHahnQ (P.comp (C (-1)*X+C 1))=_
  congr 2
  simp only [map_neg,map_one]
  ring

theorem atInf_rfPoly (P : ℚ[X]) : atInf (rfPoly P)=infPolyHahnQ P := by
  rw [atInf_eq_hom]
  exact RatFunc.liftRingHom_algebraMap _ _ P

theorem polyHahnQ_coeff (P : ℚ[X]) (n : ℕ) : (polyHahnQ P).coeff (n:ℤ)=P.coeff n := by
  change (HahnSeries.ofPowerSeries ℤ ℚ (P:PowerSeries ℚ)).coeff (n:ℤ)=_
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  exact Polynomial.coeff_coe _ _

theorem polyHahnQ_nonneg (P : ℚ[X]) : Oge (polyHahnQ P) 0 := by
  intro e he
  change (HahnSeries.ofPowerSeries ℤ ℚ (P:PowerSeries ℚ)).coeff e=0
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨n,hn⟩
  change (n:ℤ)=e at hn
  omega

theorem infPolyHahnQ_monomial (n : ℕ) (q : ℚ) :
    infPolyHahnQ (monomial n q)=HahnSeries.single (-(n:ℤ)) q := by
  simp only [infPolyHahnQ,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_monomial]
  have hc : algebraMap ℚ (HahnSeries ℤ ℚ) q=HahnSeries.single 0 q := by
    change algebraMap ℚ (HahnSeries ℤ ℚ) q=HahnSeries.C q
    simp only [eq_ratCast,map_ratCast]
  rw [hc]
  simp [hX,HahnSeries.inv_single,HahnSeries.single_pow,HahnSeries.single_mul_single]

theorem infPolyHahnQ_coeff (P : ℚ[X]) (n : ℕ) :
    (infPolyHahnQ P).coeff (-(n:ℤ))=P.coeff n := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ => simp only [map_add,HahnSeries.coeff_add,ihP,ihQ,Polynomial.coeff_add]
  | monomial k q =>
    rw [infPolyHahnQ_monomial]
    simp [HahnSeries.coeff_single,Polynomial.coeff_monomial,eq_comm]

theorem infPolyHahnQ_positive (P : ℚ[X]) (e : ℤ) (he : 0<e) : (infPolyHahnQ P).coeff e=0 := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ => simp only [map_add,HahnSeries.coeff_add,ihP,ihQ,add_zero]
  | monomial k q =>
    rw [infPolyHahnQ_monomial]
    exact HahnSeries.coeff_single_of_ne (by omega)

theorem infPolyHahnQ_order (P : ℚ[X]) : Oge (infPolyHahnQ P) (-(P.natDegree:ℤ)) := by
  intro e he
  have hen : (((-e).toNat:ℕ):ℤ)= -e := Int.toNat_of_nonneg (by omega)
  have heq : e= -(((-e).toNat:ℕ):ℤ) := by omega
  rw [heq,infPolyHahnQ_coeff]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  omega

theorem Oge.mul_coeff {f g : HahnSeries ℤ ℚ} {a b : ℤ} (hf : Oge f a) (hg : Oge g b) :
    (f*g).coeff (a+b)=f.coeff a*g.coeff b := by
  by_cases hfn : f=0
  · simp [hfn]
  by_cases hgn : g=0
  · simp [hgn]
  have hfa := hf.order hfn
  have hgb := hg.order hgn
  have hb : Oge (f*g) (f.order+g.order) := (Oge.of_order (le_refl f.order)).mul (Oge.of_order (le_refl g.order))
  by_cases ha : a=f.order
  · by_cases hc : b=g.order
    · rw [ha,hc,HahnSeries.coeff_mul_order_add_order,HahnSeries.leadingCoeff_eq,HahnSeries.leadingCoeff_eq]
    · rw [hb _ (by omega),HahnSeries.coeff_eq_zero_of_lt_order (by omega : b<g.order),mul_zero]
  · rw [hb _ (by omega),HahnSeries.coeff_eq_zero_of_lt_order (by omega : a<f.order),zero_mul]

theorem Oge.pow_coeff {f : HahnSeries ℤ ℚ} {a : ℤ} (hf : Oge f a) (n : ℕ) :
    (f^n).coeff ((n:ℤ)*a)=(f.coeff a)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul,Oge.mul_coeff (hf.pow n) hf,ih,pow_succ]

theorem hX_initial : Oge (hX : HahnSeries ℤ ℚ) 1 ∧ (hX : HahnSeries ℤ ℚ).coeff 1=1 := by
  exact ⟨Oge.single 1 1,by simp [hX]⟩
theorem one_sub_hX_initial :
    Oge (1-hX : HahnSeries ℤ ℚ) 0 ∧ (1-hX : HahnSeries ℤ ℚ).coeff 0=1 := by
  refine ⟨(Oge.C 1).sub (hX_initial.1.mono (by omega)),?_⟩
  simp [hX]
theorem inv_hX_initial :
    Oge ((hX : HahnSeries ℤ ℚ)⁻¹) (-1) ∧ ((hX : HahnSeries ℤ ℚ)⁻¹).coeff (-1)=1 := by
  have he : (hX : HahnSeries ℤ ℚ)⁻¹=HahnSeries.single (-1) 1 := by simp [hX,HahnSeries.inv_single]
  rw [he]
  exact ⟨Oge.single _ _,by simp⟩
theorem one_sub_inv_hX_initial :
    Oge (1-(hX : HahnSeries ℤ ℚ)⁻¹) (-1) ∧
      (1-(hX : HahnSeries ℤ ℚ)⁻¹).coeff (-1)= -1 := by
  refine ⟨((Oge.C 1).mono (by omega)).sub inv_hX_initial.1,?_⟩
  simp [hX,HahnSeries.inv_single]

theorem clearing_initial (x y f : HahnSeries ℤ ℚ) (D : ℚ) (nx ny ns : ℕ) (u v e : ℤ)
    (hx : Oge x u) (hy : Oge y v) (hf : Oge f e) :
    let L := (HahnSeries.C D*x^nx*y^ny)^ns*f
    let a := (ns:ℤ)*((nx:ℤ)*u+(ny:ℤ)*v)+e
    Oge L a ∧ L.coeff a=
      (D*(x.coeff u)^nx*(y.coeff v)^ny)^ns*f.coeff e := by
  dsimp only
  have hb : Oge (HahnSeries.C D*x^nx*y^ny) ((nx:ℤ)*u+(ny:ℤ)*v) := by
    simpa only [zero_add] using ((Oge.C D).mul (hx.pow nx)).mul (hy.pow ny)
  have hbc : (HahnSeries.C D*x^nx*y^ny).coeff ((nx:ℤ)*u+(ny:ℤ)*v)=
      D*(x.coeff u)^nx*(y.coeff v)^ny := by
    have hmul := ((Oge.C D).mul (hx.pow nx)).mul_coeff (hy.pow ny)
    simp only [zero_add] at hmul
    rw [hmul,hy.pow_coeff ny]
    have hconst := (Oge.C D).mul_coeff (hx.pow nx)
    simp only [zero_add] at hconst
    rw [hconst,hx.pow_coeff nx]
    rw [HahnSeries.C_apply,HahnSeries.coeff_single_same]
  refine ⟨(hb.pow ns).mul hf,?_⟩
  rw [(hb.pow ns).mul_coeff hf,hb.pow_coeff ns,hbc]

theorem atOne_rfPoly_coeff (P : ℚ[X]) (n : ℕ) :
    (atOne (rfPoly P)).coeff (n:ℤ)=(P.comp (X+1)).coeff n*(-1:ℚ)^n := by
  rw [atOne_rfPoly,polyHahnQ_coeff]
  have he : P.comp (1-X)=(P.comp (X+1)).comp (C (-1)*X) := by
    rw [Polynomial.comp_assoc]
    congr 1
    simp only [Polynomial.add_comp,Polynomial.X_comp,Polynomial.one_comp,map_neg,map_one]
    ring
  rw [he,Polynomial.comp_C_mul_X_coeff]

theorem intPolyRF_atZero_coeff (P : ℤ[X]) (n : ℕ) :
    (atZero (intPolyRF P)).coeff (n:ℤ)=(P.coeff n:ℚ) := by
  rw [intPolyRF,atZero_rfPoly,polyHahnQ_coeff,Polynomial.coeff_map]
  rfl
theorem intPolyRF_atOne_coeff (P : ℤ[X]) (n : ℕ) :
    (atOne (intPolyRF P)).coeff (n:ℤ)=((P.comp (X+1)).coeff n:ℚ)*(-1:ℚ)^n := by
  rw [intPolyRF,atOne_rfPoly_coeff]
  have he : (P.map (Int.castRingHom ℚ)).comp (X+1)=(P.comp (X+1)).map (Int.castRingHom ℚ) := by
    rw [Polynomial.map_comp]
    simp
  rw [he,Polynomial.coeff_map]
  rfl
theorem intPolyRF_atInf_coeff (P : ℤ[X]) (n : ℕ) :
    (atInf (intPolyRF P)).coeff (-(n:ℤ))=(P.coeff n:ℚ) := by
  rw [intPolyRF,atInf_rfPoly,infPolyHahnQ_coeff,Polynomial.coeff_map]
  rfl

#print axioms Oge.mul_coeff
#print axioms Oge.pow_coeff
#print axioms one_sub_inv_hX_initial
#print axioms clearing_initial
#print axioms intPolyRF_atOne_coeff
end
end CatalanCore.Li2.NVMod

