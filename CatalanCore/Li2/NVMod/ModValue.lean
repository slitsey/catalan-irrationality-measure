module
public import CatalanCore.Li2.NVMod.EndpointSeries
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

private def intPolyEmbedding : ℤ[X]→+*RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem intPolyRF_injective : Function.Injective intPolyRF :=
  (RatFunc.algebraMap_injective ℚ).comp (Polynomial.map_injective _ Int.cast_injective)

def RFValue {K : Type*} [Field K] (φ : ℤ[X]→+*K) (F : RatFunc ℚ) (v : K) : Prop :=
  ∃ P Q : ℤ[X],φ Q≠0 ∧ F=intPolyRF P/intPolyRF Q ∧ v=φ P/φ Q

theorem intPolyRF_ne_zero {K : Type*} [Field K] (φ : ℤ[X]→+*K) (P : ℤ[X])
    (h : φ P≠0) : intPolyRF P≠0 := by
  intro hz
  have hp : P=0 := intPolyRF_injective (by simpa only [intPolyRF,map_zero,Polynomial.map_zero,rfPoly] using hz)
  exact h (by rw [hp,map_zero])

theorem RFValue.intPoly {K : Type*} [Field K] (φ : ℤ[X]→+*K) (P : ℤ[X]) :
    RFValue φ (intPolyRF P) (φ P) := by
  refine ⟨P,1,by simp,?_,by simp⟩
  simp [intPolyRF,rfPoly]

theorem RFValue.unique {K : Type*} [Field K] {φ : ℤ[X]→+*K} {F : RatFunc ℚ} {v w : K}
    (hv : RFValue φ F v) (hw : RFValue φ F w) : v=w := by
  obtain ⟨P,Q,hQ,hF,hv⟩ := hv
  obtain ⟨R,S,hS,hG,hw⟩ := hw
  have hq := intPolyRF_ne_zero φ Q hQ
  have hs := intPolyRF_ne_zero φ S hS
  have he : intPolyRF P/intPolyRF Q=intPolyRF R/intPolyRF S := hF.symm.trans hG
  have hc := (div_eq_div_iff hq hs).mp he
  change intPolyEmbedding P*intPolyEmbedding S=intPolyEmbedding R*intPolyEmbedding Q at hc
  rw [←map_mul,←map_mul] at hc
  have hpoly : P*S=R*Q := intPolyRF_injective hc
  have hh := congrArg φ hpoly
  simp only [map_mul] at hh
  rw [hv,hw]
  exact (div_eq_div_iff hQ hS).mpr hh

theorem RFValue.add {K : Type*} [Field K] {φ : ℤ[X]→+*K} {F G : RatFunc ℚ} {v w : K}
    (hF : RFValue φ F v) (hG : RFValue φ G w) : RFValue φ (F+G) (v+w) := by
  obtain ⟨P,Q,hQ,hF,hv⟩ := hF
  obtain ⟨R,S,hS,hG,hw⟩ := hG
  refine ⟨P*S+R*Q,Q*S,by simpa only [map_mul] using mul_ne_zero hQ hS,?_,?_⟩
  · rw [hF,hG]
    change intPolyEmbedding P/intPolyEmbedding Q+intPolyEmbedding R/intPolyEmbedding S=
      intPolyEmbedding (P*S+R*Q)/intPolyEmbedding (Q*S)
    simp only [map_add,map_mul]
    have hq : intPolyEmbedding Q≠0 := intPolyRF_ne_zero φ Q hQ
    have hs : intPolyEmbedding S≠0 := intPolyRF_ne_zero φ S hS
    field_simp
  · rw [hv,hw]
    simp only [map_add,map_mul]
    field_simp

theorem RFValue.mul {K : Type*} [Field K] {φ : ℤ[X]→+*K} {F G : RatFunc ℚ} {v w : K}
    (hF : RFValue φ F v) (hG : RFValue φ G w) : RFValue φ (F*G) (v*w) := by
  obtain ⟨P,Q,hQ,hF,hv⟩ := hF
  obtain ⟨R,S,hS,hG,hw⟩ := hG
  refine ⟨P*R,Q*S,by simpa only [map_mul] using mul_ne_zero hQ hS,?_,?_⟩
  · rw [hF,hG]
    change intPolyEmbedding P/intPolyEmbedding Q*(intPolyEmbedding R/intPolyEmbedding S)=
      intPolyEmbedding (P*R)/intPolyEmbedding (Q*S)
    simp only [map_mul,div_mul_div_comm]
  · rw [hv,hw]
    simp only [map_mul,div_mul_div_comm]

theorem RFValue.inv {K : Type*} [Field K] {φ : ℤ[X]→+*K} {F : RatFunc ℚ} {v : K}
    (hF : RFValue φ F v) (hv : v≠0) : RFValue φ F⁻¹ v⁻¹ := by
  obtain ⟨P,Q,hQ,hF,he⟩ := hF
  have hP : φ P≠0 := by intro hz;rw [he,hz,zero_div] at hv; exact hv rfl
  exact ⟨Q,P,hP,by rw [hF,inv_div],by rw [he,inv_div]⟩

theorem RFValue.pow {K : Type*} [Field K] {φ : ℤ[X]→+*K} {F : RatFunc ℚ} {v : K}
    (hF : RFValue φ F v) (n : ℕ) : RFValue φ (F^n) (v^n) := by
  obtain ⟨P,Q,hQ,hF,hv⟩ := hF
  refine ⟨P^n,Q^n,by simpa only [map_pow] using pow_ne_zero n hQ,?_,?_⟩
  · rw [hF,div_pow]
    change (intPolyEmbedding P)^n/(intPolyEmbedding Q)^n=
      intPolyEmbedding (P^n)/intPolyEmbedding (Q^n)
    simp only [map_pow]
  · simp only [hv,div_pow,map_pow]

theorem RFValue.nat {K : Type*} [Field K] (φ : ℤ[X]→+*K) (n : ℕ) :
    RFValue φ (n:RatFunc ℚ) (n:K) := by
  have h := RFValue.intPoly φ (n:ℤ[X])
  change RFValue φ (intPolyEmbedding (n:ℤ[X])) (φ (n:ℤ[X])) at h
  simpa only [map_natCast] using h

theorem RFValue.int {K : Type*} [Field K] (φ : ℤ[X]→+*K) (n : ℤ) :
    RFValue φ (n:RatFunc ℚ) (n:K) := by
  have h := RFValue.intPoly φ (n:ℤ[X])
  change RFValue φ (intPolyEmbedding (n:ℤ[X])) (φ (n:ℤ[X])) at h
  simpa only [map_intCast] using h

theorem RFValue.neg {K : Type*} [Field K] {φ : ℤ[X]→+*K} {F : RatFunc ℚ} {v : K}
    (hF : RFValue φ F v) : RFValue φ (-F) (-v) := by
  simpa only [Int.cast_neg,Int.cast_one,neg_one_mul] using (RFValue.int φ (-1)).mul hF

theorem RFValue.sub {K : Type*} [Field K] {φ : ℤ[X]→+*K} {F G : RatFunc ℚ} {v w : K}
    (hF : RFValue φ F v) (hG : RFValue φ G w) : RFValue φ (F-G) (v-w) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem RFValue.div {K : Type*} [Field K] {φ : ℤ[X]→+*K} {F G : RatFunc ℚ} {v w : K}
    (hF : RFValue φ F v) (hG : RFValue φ G w) (hw : w≠0) : RFValue φ (F/G) (v/w) := by
  simpa only [div_eq_mul_inv] using hF.mul (hG.inv hw)

theorem RFValue.sum {K : Type*} [Field K] {φ : ℤ[X]→+*K} {ι : Type*}
    (S : Finset ι) (f : ι→RatFunc ℚ) (v : ι→K) (h : ∀ i∈S,RFValue φ (f i) (v i)) :
    RFValue φ (∑ i∈S,f i) (∑ i∈S,v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,Nat.cast_zero] using RFValue.nat φ 0
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))

theorem RFValue.zpow {K : Type*} [Field K] {φ : ℤ[X]→+*K} {F : RatFunc ℚ} {v : K}
    (hF : RFValue φ F v) (hv : v≠0) (n : ℤ) : RFValue φ (F^n) (v^n) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using hF.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hF.pow (n+1)).inv (pow_ne_zero _ hv)

#print axioms intPolyRF_injective
#print axioms RFValue.unique
#print axioms RFValue.add
#print axioms RFValue.mul
#print axioms RFValue.inv
#print axioms RFValue.sum
#print axioms RFValue.zpow
end
end CatalanCore.Li2.NVMod
