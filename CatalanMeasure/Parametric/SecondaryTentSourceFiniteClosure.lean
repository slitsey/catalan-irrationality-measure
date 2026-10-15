module
public import CatalanMeasure.Parametric.SecondaryTentSourceReflection
public import CatalanMeasure.Parametric.SecondaryTentSourceWeightedTrace

/-! Uniqueness of finite Laurent source expressions closes coefficient extraction. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped LaurentPolynomial
noncomputable section

theorem secondaryTent_source_reflected_unique {p : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (L : (ZMod p)[T;T⁻¹]) (S : (ZMod p)[X])
    (a : ZMod p) (m : ℕ)
    (he : secondaryTentSourceEvaluate p hp2 L =
      algebraMap (ZMod p) (RatFunc (ZMod p)) a *
        S.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)⁻¹ *
          (palindromicRatT p)^m) : L.coeff 0=a*S.coeff m := by
  have hl : L=a • secondaryTentSourceReflected S m := by
    apply secondaryTent_source_laurent_eval_injective hp2
    change secondaryTentSourceEvaluate p hp2 L = _
    rw [he, LaurentPolynomial.smul_eq_C_mul, map_mul]
    simp only [secondaryTentSourceEvaluate, LaurentPolynomial.eval₂_C]
    rw [secondaryTent_source_reflected_eval]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, mul_assoc]
  rw [hl]
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    secondaryTent_source_reflected_coeff]

theorem secondaryTent_source_signed_trace_scale {K : Type*} [Field K]
    {N p e : ℕ} (hN : 0<N) (hp : 0<p) (he : e<p)
    (x s F E H h u v A B : K) (h2 : (2:K)≠0) (hx : x≠0) (hF : F≠0)
    (hjac : F = -s/x)
    (hpair : F*E = x^e*(2^(26*N)*h/2)*(u*(B-s*A/x)^p-v*(B+s*A/x)^p))
    (htrace : h*(u*(B-s*A/x)^p-v*(B+s*A/x)^p)=8*s*H/x^(6*p)) :
    E = (-8*2^(26*N-1))*H/x^(6*p-1-e) := by
  have hexp : 6*p=e+1+(6*p-1-e) := by omega
  have hpow : x^(6*p)=x^e*x*x^(6*p-1-e) := by
    conv_lhs => rw [hexp, pow_add, pow_add, pow_one]
  have htwo : (2:K)^(26*N)/2=2^(26*N-1) := by
    have hne : 26*N-1+1=26*N := by omega
    calc
      _ = (2^(26*N-1)*2)/2 := by congr 1; rw [← pow_succ,hne]
      _ = _ := mul_div_cancel_right₀ _ h2
  have hcore : x^e*(8*s*H/x^(6*p)) = -8*F*H/x^(6*p-1-e) := by
    rw [hpow,hjac]
    field_simp [hx]
    <;> ring
  apply mul_left_cancel₀ hF
  calc
    F*E = (2^(26*N)/2)*(x^e*(h*(u*(B-s*A/x)^p-v*(B+s*A/x)^p))) := by
      rw [hpair]; ring
    _ = _ := by rw [htrace,hcore,htwo]; ring

end
end CatalanMeasure.Parametric
