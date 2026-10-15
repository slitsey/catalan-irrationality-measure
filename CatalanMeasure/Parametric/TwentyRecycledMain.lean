module
public import CatalanMeasure.Parametric.TwentyMain
public import CatalanMeasure.Parametric.TwentyFullPerturbation
public import CatalanMeasure.Parametric.TwentyCoefficientDivisibility
public import CatalanMeasure.RecycledPNTWindow
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Polynomial Filter Real
open scoped BigOperators Topology Nat
noncomputable section

theorem twentyMeasureIntPoly_full_hypotheses {η : ℝ} (hη : η<400*twentyMeasureGap) :
    ∃ P₀ : ℕ,
      (∀ p,P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ),0<b → ¬p^2∣b →
        aeval ((a:ℝ)/b) (twentyMeasureIntPoly p)≠0) ∧
      (∀ p,P₀ ≤ p → p.Prime → ∀ x : ℝ,|x-catalan| ≤ Real.exp (-(108*(p:ℝ))) →
        |aeval x (twentyMeasureIntPoly p)| ≤ Real.exp (-(η*(p:ℝ)^2))) :=by
  let e : ℝ :=(400*twentyMeasureGap-η)/1600
  have he : 0<e :=by unfold e;linarith only [hη]
  have h2 :=positive_polynomial_factor_eventually (2:ℝ) (by norm_num) 0 (ε :=e) he
  have hev : ∀ᶠ p : ℕ in atTop,finitePrimeCutoff twenty<p ∧ 1000000000000 ≤ p ∧
      (∀ x : ℝ,|x-catalan| ≤ Real.exp (-(108*(p:ℝ))) →
        |aeval x (twentyMeasureIntPoly p)| ≤ Real.exp (-(η*(p:ℝ)^2))) :=by
    filter_upwards [twenty_full_perturbation he,twenty_base_bound_eventually he,
      twenty_log_denomBound_eventually_le he,twenty_factorial_eventually he,h2,
      eventually_gt_atTop (finitePrimeCutoff twenty),eventually_ge_atTop (1000000000000:ℕ)]
      with p hpert hbase hden hfac htwo hcut hbig
    refine ⟨hcut,hbig,?_⟩
    intro x hx
    have hp : 0<p :=by omega
    have hp1 : (1:ℝ) ≤ p :=by exact_mod_cast hp
    let E : ℝ :=(20*(p:ℝ))^2*(-twentyDualTarget+Real.log 2/2+e)
    have hΔ : |aeval x (deltaPoly twenty p)| ≤ 2*Real.exp E :=by
      calc
        _ = |(aeval x (deltaPoly twenty p)-aeval catalan (deltaPoly twenty p))+
          aeval catalan (deltaPoly twenty p)| :=by rw [sub_add_cancel]
        _ ≤ |aeval x (deltaPoly twenty p)-aeval catalan (deltaPoly twenty p)|+
          |aeval catalan (deltaPoly twenty p)| :=abs_add_le _ _
        _ ≤ Real.exp E+Real.exp E :=add_le_add (hpert x hx) hbase
        _ = _ :=by ring
    have hD : (twentyDenomBound p:ℝ) ≤
        Real.exp ((8795/4800+(21/200)*Real.log 2+e)*(20*(p:ℝ))^2) :=by
      rw [← Real.exp_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (twentyDenomBound_ne_zero p)))]
      exact Real.exp_le_exp.mpr hden
    have htwo' : (2:ℝ) ≤ Real.exp (e*(20*(p:ℝ))^2) :=by
      simp only [pow_zero,mul_one] at htwo
      have hs : (p:ℝ) ≤ (20*(p:ℝ))^2 :=by nlinarith only [hp1]
      exact htwo.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs he.le))
    rw [aeval_twentyMeasureIntPoly hbig,abs_mul,abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((18*p)!:ℝ)),
      abs_of_nonneg (Nat.cast_nonneg (twentyDenomBound p))]
    calc
      _ ≤ Real.exp (e*(20*(p:ℝ))^2)*
          Real.exp ((8795/4800+(21/200)*Real.log 2+e)*(20*(p:ℝ))^2)*
          (2*Real.exp E) :=by gcongr
      _ ≤ Real.exp (e*(20*(p:ℝ))^2)*
          Real.exp ((8795/4800+(21/200)*Real.log 2+e)*(20*(p:ℝ))^2)*
          (Real.exp (e*(20*(p:ℝ))^2)*Real.exp E) :=by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right htwo' (Real.exp_pos _).le) (by positivity)
      _ = _ :=by
        rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
        congr 1
        unfold E e twentyMeasureGap
        ring
  obtain ⟨P₀,hP₀⟩ :=eventually_atTop.mp hev
  refine ⟨P₀,?_,?_⟩
  · intro p hp hprime a b hb hpb
    haveI : Fact p.Prime :=⟨hprime⟩
    exact twentyMeasureIntPoly_nonvanishing (hP₀ p hp).2.1 (hP₀ p hp).1 a hb hpb
  · intro p hp _
    exact (hP₀ p hp).2.2

/-- The full-interval marked bound and coefficient recycling, combined. -/
theorem catalan_irrationalityMeasure_1099 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ)^(-(1099 : ℝ)) < |catalan-(a : ℝ)/b| := by
  obtain ⟨P₁, hnz, hsmall⟩ := twentyMeasureIntPoly_full_hypotheses twenty_measure_eta_lt
  let P₀ := max P₁ 1000000000000
  have hnz' : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p^2 ∣ b →
      aeval ((a : ℝ)/b) (twentyMeasureIntPoly p) ≠ 0 := by
    intro p hp hprime
    exact hnz p (le_trans (le_max_left _ _) hp) hprime
  have hsmall' : ∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ,
      |x-catalan| ≤ Real.exp (-(108*(p : ℝ))) →
      |aeval x (twentyMeasureIntPoly p)| ≤ Real.exp (-((177/100 : ℝ)*(p : ℝ)^2)) := by
    intro p hp hprime
    exact hsmall p (le_trans (le_max_left _ _) hp) hprime
  have hcoeff : ∀ p, P₀ ≤ p → p.Prime → ∀ q : ℕ,
      q.Prime → p < q → q ≤ 2*p → ∀ i ≤ 18*p,
      (q : ℤ)^(2*i) ∣ (twentyMeasureIntPoly p).coeff i := by
    intro p hp _ q hq hpq hq2p i _
    haveI : Fact q.Prime := ⟨hq⟩
    exact twentyMeasureIntPoly_coeff_prime_pow_dvd
      (le_trans (le_max_right _ _) hp) hpq hq2p i
  have hh := CatalanMeasure.irrationality_measure_of_recycled_polynomials_square_pnt
    catalan 18 (η := 177/100) (ρ := 108) (κ := 1099/108) (δ := 1/100000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    twentyMeasureIntPoly P₀ twentyMeasureIntPoly_natDegree_le hnz' hcoeff hsmall'
  convert hh using 1 <;> norm_num

end
end CatalanMeasure.Parametric
