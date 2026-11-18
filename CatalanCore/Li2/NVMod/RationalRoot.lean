module
public import CatalanCore.Li2.NVMod.CheckerSound
public import CatalanCore.Li2.NVMod.ModValue
public import Mathlib.RingTheory.Polynomial.RationalRoot
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

theorem RFValue.eval_intPoly {K : Type*} [Field K] {φ : ℤ[X]→+*K} {F : RatFunc ℚ} {v : K}
    (hF : RFValue φ F v) (P : ℤ[X]) :
    RFValue φ (P.eval₂ (Int.castRingHom (RatFunc ℚ)) F) (P.eval₂ (Int.castRingHom K) v) := by
  simp only [Polynomial.eval₂_eq_sum]
  change RFValue φ (∑ k∈P.support,(P.coeff k:RatFunc ℚ)*F^k)
    (∑ k∈P.support,(P.coeff k:K)*v^k)
  apply RFValue.sum
  intro k hk
  exact (RFValue.int φ (P.coeff k)).mul (hF.pow k)

theorem eval_intPoly_ratCast (P : ℤ[X]) (z : ℚ) :
    P.eval₂ (Int.castRingHom (RatFunc ℚ)) (z:RatFunc ℚ)=
      algebraMap ℚ (RatFunc ℚ) ((P.map (Int.castRingHom ℚ)).eval z) := by
  have h := Polynomial.eval₂_at_apply (p:=P.map (Int.castRingHom ℚ)) (algebraMap ℚ (RatFunc ℚ)) z
  rw [Polynomial.eval₂_map] at h
  have hc : (algebraMap ℚ (RatFunc ℚ)).comp (Int.castRingHom ℚ)=Int.castRingHom (RatFunc ℚ) :=
    Subsingleton.elim _ _
  rw [hc] at h
  simpa only [eq_ratCast] using h

theorem rational_root_mod (P : ℤ[X]) (p : ℕ) [Fact p.Prime] (z : ℚ) (a d : ℤ)
    (hz : z=(a:ℚ)/(d:ℚ)) (hd : (d:ZMod p)≠0)
    (hroot : (P.map (Int.castRingHom ℚ)).eval z=0) :
    (P.map (Int.castRingHom (ZMod p))).eval ((a:ZMod p)/(d:ZMod p))=0 := by
  let r : ZMod p := (a:ZMod p)/(d:ZMod p)
  let φ : ℤ[X]→+*ZMod p := Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) r
  have hzf : (z:RatFunc ℚ)=(a:RatFunc ℚ)/(d:RatFunc ℚ) := by
    simpa only [Rat.cast_div,Rat.cast_intCast] using congrArg (fun q : ℚ=>(q:RatFunc ℚ)) hz
  have hv : RFValue φ (z:RatFunc ℚ) r := by
    rw [hzf]
    exact (RFValue.int φ a).div (RFValue.int φ d) hd
  have he := hv.eval_intPoly P
  rw [eval_intPoly_ratCast,hroot,map_zero] at he
  have hzero : RFValue φ (0:RatFunc ℚ) (0:ZMod p) := by simpa using RFValue.nat φ 0
  simpa only [Polynomial.eval_map] using he.unique hzero

theorem no_rational_root_of_residues (F : ℤ[X]) (p v0 v1 : ℕ) [Fact p.Prime]
    (h0 : X^v0∣F) (h1 : (X-1)^v1∣F)
    (he0 : ¬(p:ℤ)∣F.coeff v0) (he1 : ¬(p:ℤ)∣(F.comp (X+1)).coeff v1)
    (heInf : ¬(p:ℤ)∣F.leadingCoeff)
    (hint : ∀ r : ZMod p, r≠0 → r≠1 → (F.map (Int.castRingHom (ZMod p))).eval r≠0) :
    ∀ z : ℚ, z≠0 → z≠1 → (F.map (Int.castRingHom ℚ)).eval z≠0 := by
  intro z hz0 hz1 hroot
  have haeval : aeval z F=0 := by
    rw [Polynomial.aeval_def]
    have hf : algebraMap ℤ ℚ=Int.castRingHom ℚ := Subsingleton.elim _ _
    rw [hf,←Polynomial.eval_map]
    exact hroot
  let a : ℤ := IsFractionRing.num ℤ z
  let d : ℤ := IsFractionRing.den ℤ z
  have hrepr : z=(a:ℚ)/(d:ℚ) := (IsFractionRing.mk'_num_den' ℤ z).symm
  have hddvd : d∣F.leadingCoeff := den_dvd_of_is_root haeval
  have hdu : (d:ZMod p)≠0 := by
    intro hd
    exact heInf (((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd).trans hddvd)
  let r : ZMod p := (a:ZMod p)/(d:ZMod p)
  have hmod := rational_root_mod F p z a d hrepr hdu hroot
  by_cases hr0 : r=0
  · obtain ⟨G,hG⟩ := h0
    have hgroot : (G.map (Int.castRingHom ℚ)).eval z=0 := by
      rw [hG,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,
        Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X] at hroot
      exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hz0)
    have hgmod := rational_root_mod G p z a d hrepr hdu hgroot
    change (G.map (Int.castRingHom (ZMod p))).eval r=0 at hgmod
    rw [hr0,←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_map] at hgmod
    have hcoeff : F.coeff v0=G.coeff 0 := by
      rw [hG]
      simpa only [zero_add] using Polynomial.coeff_X_pow_mul G v0 0
    rw [hcoeff] at he0
    exact he0 ((ZMod.intCast_zmod_eq_zero_iff_dvd (G.coeff 0) p).mp hgmod)
  · by_cases hr1 : r=1
    · obtain ⟨G,hG⟩ := h1
      have hgroot : (G.map (Int.castRingHom ℚ)).eval z=0 := by
        rw [hG,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_X,
          Polynomial.map_one,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,
          Polynomial.eval_X,Polynomial.eval_one] at hroot
        exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hz1))
      have hgmod := rational_root_mod G p z a d hrepr hdu hgroot
      change (G.map (Int.castRingHom (ZMod p))).eval r=0 at hgmod
      rw [hr1,Polynomial.eval_one_map] at hgmod
      have hcomp : F.comp (X+1)=X^v1*G.comp (X+1) := by
        rw [hG,Polynomial.mul_comp,Polynomial.pow_comp]
        simp
      have hcoeff : (F.comp (X+1)).coeff v1=G.eval 1 := by
        rw [hcomp]
        have hc := Polynomial.coeff_X_pow_mul (G.comp (X+1)) v1 0
        rw [zero_add] at hc
        rw [hc,Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_comp]
        simp
      rw [hcoeff] at he1
      exact he1 ((ZMod.intCast_zmod_eq_zero_iff_dvd (G.eval 1) p).mp hgmod)
    · exact hint r hr0 hr1 hmod

#print axioms rational_root_mod
#print axioms no_rational_root_of_residues
end
end CatalanCore.Li2.NVMod
