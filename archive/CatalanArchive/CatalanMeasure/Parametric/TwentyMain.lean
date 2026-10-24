module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyIntegerPolynomial
public import CatalanArchive.CatalanMeasure.Parametric.TwentyPerturbation
public import CatalanMeasure.SquarePNTWindow
public import CatalanMeasure.Criterion
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Polynomial Filter Real
open scoped BigOperators Topology Nat
noncomputable section

def twentyMeasureGap : ℝ :=twentyDualTarget-Real.log 2/2-
  (8795/4800+(21/200)*Real.log 2)

theorem twenty_measure_eta_lt : (177/100:ℝ)<400*twentyMeasureGap :=by
  have hh :=twenty_eta_budget
  unfold twentyMeasureGap
  convert hh using 1 <;> ring

theorem twenty_factorial_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,((18*N)!:ℝ) ≤ Real.exp (ε*(20*(N:ℝ))^2) :=by
  have hh :=factorial_n_le_exp (c :=25*ε/144) (by positivity)
  filter_upwards [hh] with N hN
  calc
    _ ≤ ((OAI.InternalCatalan.n N)!:ℝ) :=by
      exact_mod_cast Nat.factorial_le (by unfold OAI.InternalCatalan.n;omega : 18*N ≤ OAI.InternalCatalan.n N)
    _ ≤ _ :=hN
    _ = _ :=by simp only [OAI.InternalCatalan.n,Nat.cast_mul,Nat.cast_ofNat];congr 1;ring

theorem twentyMeasureIntPoly_nonvanishing {p : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ p) (hcut : finitePrimeCutoff twenty<p)
    (a : ℤ) {b : ℕ} (hb : 0<b) (hpb : ¬p^2∣b) :
    aeval ((a:ℝ)/b) (twentyMeasureIntPoly p)≠0 :=by
  rw [aeval_twentyMeasureIntPoly hbig]
  have hx : (a:ℝ)/b=(((a:ℚ)/b:ℚ):ℝ) :=by
    rw [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  rw [hx,aeval_ratCast_eq,eval_deltaPoly]
  have hd :=TwentyBase.twenty_prime_nonvanishing hcut ((a:ℚ)/b)
    (prime_mul_div_den_unit a hb hpb)
  have hf : ((18*p)!:ℝ)≠0 :=by exact_mod_cast (Nat.factorial_pos _).ne'
  have hD : (twentyDenomBound p:ℝ)≠0 :=by exact_mod_cast twentyDenomBound_ne_zero p
  have hdR : (determinantRat twenty ((a:ℚ)/b) p:ℝ)≠0 :=by exact_mod_cast hd
  exact mul_ne_zero (mul_ne_zero hf hD) hdR

theorem twentyMeasureIntPoly_hypotheses {η : ℝ} (hη : η<400*twentyMeasureGap) :
    ∃ P₀ : ℕ,
      (∀ p,P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ),0<b → ¬p^2∣b →
        aeval ((a:ℝ)/b) (twentyMeasureIntPoly p)≠0) ∧
      (∀ p,P₀ ≤ p → p.Prime → ∀ x : ℝ,|x-catalan| ≤ Real.exp (-(120*(p:ℝ))) →
        |aeval x (twentyMeasureIntPoly p)| ≤ Real.exp (-(η*(p:ℝ)^2))) :=by
  let e : ℝ :=(400*twentyMeasureGap-η)/1600
  have he : 0<e :=by unfold e;linarith only [hη]
  have h2 :=positive_polynomial_factor_eventually (2:ℝ) (by norm_num) 0 (ε :=e) he
  have hev : ∀ᶠ p : ℕ in atTop,finitePrimeCutoff twenty<p ∧ 1000000000000 ≤ p ∧
      (∀ x : ℝ,|x-catalan| ≤ Real.exp (-(120*(p:ℝ))) →
        |aeval x (twentyMeasureIntPoly p)| ≤ Real.exp (-(η*(p:ℝ)^2))) :=by
    filter_upwards [twenty_perturbation e he,twenty_base_bound_eventually he,
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

theorem catalan_irrationalityMeasure_1281 :
    ∀ᶠ b : ℕ in atTop,∀ a : ℤ,(b:ℝ)^(-(1281:ℝ)) < |catalan-(a:ℝ)/b| :=by
  obtain ⟨P₀,hnz,hsmall⟩ :=twentyMeasureIntPoly_hypotheses twenty_measure_eta_lt
  have hh :=CatalanMeasure.irrationality_measure_of_polynomials_square_pnt catalan 18
    (η :=177/100) (ρ :=120) (ε :=247/5000) (c :=1001/1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    twentyMeasureIntPoly P₀ twentyMeasureIntPoly_natDegree_le hnz hsmall
  simp only [Nat.cast_ofNat] at hh
  have he : (1+247/5000:ℝ)*120*max (18/(177/100)) ((1001/1000)/(2*(247/5000)))=
      (377784/295:ℝ) :=by norm_num
  rw [he] at hh
  filter_upwards [hh,eventually_ge_atTop (2:ℕ)] with b hb hb2 a
  have hb1 : (1:ℝ) ≤ b :=by exact_mod_cast (show 1 ≤ b by omega)
  exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)) (hb a)

theorem catalan_irrationalityMeasure_3662 :
    ∀ᶠ b : ℕ in atTop,∀ a : ℤ,(b:ℝ)^(-(3662:ℝ)) < |catalan-(a:ℝ)/b| :=by
  obtain ⟨P₀,hnz,hsmall⟩ :=twentyMeasureIntPoly_hypotheses twenty_measure_eta_lt
  have hnz' : ∀ p,P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ),0<b → ¬p∣b →
      aeval ((a:ℝ)/b) (twentyMeasureIntPoly p)≠0 :=by
    intro p hp hprime a b hb hpb
    exact hnz p hp hprime a b hb (fun h =>hpb (dvd_trans (show p∣p^2 by exact ⟨p,by ring⟩) h))
  have hh :=CatalanMeasure.irrationality_measure_of_polynomials catalan 18
    (η :=177/100) (ρ :=120) (by norm_num) (by norm_num)
    twentyMeasureIntPoly P₀ twentyMeasureIntPoly_natDegree_le hnz' hsmall
  simp only [Nat.cast_ofNat] at hh
  have he : (3:ℝ)*120*max (18/(177/100)) 4=(216000/59:ℝ) :=by norm_num
  rw [he] at hh
  filter_upwards [hh,eventually_ge_atTop (2:ℕ)] with b hb hb2 a
  have hb1 : (1:ℝ) ≤ b :=by exact_mod_cast (show 1 ≤ b by omega)
  exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)) (hb a)

end
end CatalanMeasure.Parametric
